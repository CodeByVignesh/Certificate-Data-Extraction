import os
from datetime import datetime
import sys
from os import mkdir, path

import pytesseract
from pdf2image import convert_from_path
import more_itertools as mit
import json
from langdetect import detect
import re
import cv2
from fuzzywuzzy.process import dedupe
from fuzzywuzzy import fuzz

import pycountry
from collections import OrderedDict

from dateutil.parser import parse

import gettext

import numpy as np
import logging
from logging.handlers import TimedRotatingFileHandler

import configparser

german = gettext.translation('iso3166', pycountry.LOCALES_DIR, languages=['de'])
german.install()
_ = german.gettext


"""Creating Logs folder"""
log_folder= "./Logs"
#if not os.path.isdir(log_folder):
#    os.mkdir(log_folder)

logger = logging.getLogger('info')
logger.setLevel(logging.INFO)
formatter = logging.Formatter(fmt='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',datefmt='%m-%d-%y %H:%M:%S')
ts = datetime.now().strftime("_%Y_%m_%dT%I_%M_%S_%p")
fh = TimedRotatingFileHandler(str(log_folder) + '/Log' + ts + '.txt', when='midnight', interval=1)
fh.setFormatter(formatter)
logger.addHandler(fh)

def WriteToLogs(Text_Log):
    '''Declaring the logging method and instantiating the same'''
    print(Text_Log)
    logger.info(str(Text_Log))
    return True

"""Reading configuration file"""
config = configparser.ConfigParser()
config.read(r'config.ini')

input_pdf_path = "".join([config['directory']['input_pdf'], "/"])
pdf_to_jpg_path = "".join([config['directory']['pdf_to_jpg'], "/"])
ocr_output_path = "".join([config['directory']['ocr_output'], "/"])
all_separate_json = "".join([config['directory']['all_pdf_json'], "/"])
clubbed_json = "".join([config['directory']['clubbed_json'], "/"])
result_csv_path = "".join([config['directory']['result_csv'], "/"])
result_path = "".join([config['directory']['result'], "/"])

tesseract_path = config['directory']['tesseract_path']
tessdata_path = config['directory']['tessdata_path']

os.environ['TESSDATA_PREFIX'] = tessdata_path


"""Description patterns"""
description_pattern=[
  'scope:',
  'this certificate is valid for the following scope:',
  'quality management system for the',
  'for the following activities',
  'the scope of this approval is applicable to:',
  'scope of certification:',
  'quality management system for',
  'scope',
  'the quality management system is applicable to the following:',
  "applicable to:",
  "product description:",
  "certification covers",
  'rem. loc. function:',
  'has established and applies in the field of',
  'has established and applied a quality management system for',
  'a quality management system for',
  'has established and applies an environmental management system for',
  'an environmental management system for'
  'Umfang:',
  'Dieses Zertifikat gilt für folgenden Geltungsbereich:',
  'Qualitätsmanagementsystem für die',
  'für die folgenden Aktivitäten',
  'Der Geltungsbereich dieser Genehmigung gilt für:',
  'Zertifizierungsumfang:',
  'Qualitätsmanagementsystem für',
  'Umfang',
  'Das Qualitätsmanagementsystem gilt für Folgendes:',
  "anwendbar auf:",
  "Produktbeschreibung:",
  "Zertifizierungsabdeckungen",
  'rem. Standortfunktionen:',
  'hat etabliert und gilt im Bereich der:',
  'Geltungsbereich:',
  'Für den Geltungsbereich:',
  "Geltungsbereich"
]
description_pattern = [pattern.lower() for pattern in description_pattern]
description_pattern_string = '|'.join(description_pattern)
description_compiled_pattern = re.compile(description_pattern_string)


"""certificate registration number patterns"""
registration_number_pattern=[
    'Certificate Registration No:',
    'Das Anschlusszertifikat Nr.',
    'Certificate identity number:',
    'Certificat enregistr sous le n*',
    'IATF No.',
    'Das Zertifikat Nr.',
    'Main certificate registration no.',
    'Certificate Registration No.:',
    'Zertifikat Nr:',
    'certificate No.',
    'certificate no.:',
    'Zertifikat-Registrier-Nr.',
    'Certificate registration No.',
    'Certificate Registration No.',
    'Zertifizierung-Nr.:',
    'Lertifikat-Registrier-Nr.',
    'Certificate N. Versione:',
    'Certificate registration no.',
    'Zertifikat-Registrier-Nr.:',
    'Registrier-Nr.:',
    'Zertifikats-Nr.:',
    'Zertifikat-Nr.:',
    'EORI-Nummer:',
    'Certificate number:',
    'Certificate',
    'Registration Number',
    'Registriernummer',
    'Zertifikat-Reg.-Nr.',
    'Zertifikat-Reg.-Nr.:',
    'Registration No.',
    'Zertifikat ',
  ]
registration_number_pattern_string = '|'.join(registration_number_pattern)
registration_number_compiled_pattern = re.compile(registration_number_pattern_string)

certificate_date_patterns = [
  'Rev.',
  'ist',
  'is',
  'Gltig',
  'Valable',
  'Valid',
  'Datum:'
]

certificate_date_pattern = '|'.join(certificate_date_patterns)
certificate_word = re.compile(certificate_date_pattern)

def get_certificate_type(content):
    """
    Find certificate keywords, such as "ISO 9001: 2008", "ISO 16949: 2009"
    """
    only_nonDuplicates = []
    try:
        for line in content.splitlines():
            # search for lines that contain certificate id
            if "9001" in line or "16949" in line or "14001" in line or "45001" in line or "50001" in line or "18001" in line:   
                s_line = ""
                lines = line.split()
                for l in lines:
                    if l.isalpha():
                        s_line = s_line + l + " "
                    else:
                        s_line = s_line + l
                certificate = re.search(r"(ISO|IATF|OHSAS).(9001|16949|14001|45001|50001|18001)?.(\d{0,4})", s_line)    
                if certificate:  
                    temp = certificate[0]
                    temp = re.sub("[-()#/@;<>`+=~|.!?,]", "", temp)
                    tt = temp.replace(":","")
                    tt = tt.replace(" ", "")
                    if tt.isalnum() == True:
                        only_nonDuplicates.append(certificate[0])             
            else:
                #If the keywords are not found then go to the next line
                continue
        if only_nonDuplicates:
            f_type = only_nonDuplicates[0]
            for only in only_nonDuplicates:
                if ":" in only:
                    f_type = only
            return f_type
        else:
            return None
    except Exception as exp:
        WriteToLogs("[Error] : The get_certificate_name function in Certificate_segregator class ran into an error : {}".format(exp))
        return {}

def _exists_country_name(s):
    """
    check whether a country name (in English or German) or country abbreviation is in the string
    e.g. Germany, Deutschland, People's Republic of China, United States, USA
    """
    for country in pycountry.countries:
        #if country.name in s or _(country.name).decode("utf-8") in s:
        if (type(country.name) == str) and (country.name in s):
            return True
        elif (type(_(country.name)) == bytes) and (_(country.name).decode("utf-8")) in s:
            return True
        try:
            if country.official_name in s:
                return True
        except:
            pass
        if country.alpha_3 in s.replace(".", ""):
            return True
        # if (type(_(country.name)) == bytes):
        #     name_in_german = _(country.name).decode("utf-8").lower()
        #     umlauts = [(u"ä", u"a"), (u"ö", u"o"), (u"ü", u"u"), (u"ß", u"ss")]
        #     for item in umlauts:
        #         name_in_german = name_in_german.replace(item[0], item[1])
        #     if name_in_german in s.lower():
        #         return True
    return False


def _exists_house_number_and_road(s):
    """
    check whether house number and road in the string
    """
    road_keywords = [u"strafe",u"strabe",u"straße", u"strare", u"strafse", u"weg", u"platz", u"avenue",u"lane",u"road",u"district",u"boulevard",u"drive",u"street",u"ave"]
    if any(w in s.lower() for w in road_keywords):
        return True
    return False

def has_numbers(inputString):
    return any(char.isdigit() for char in inputString)

def has_word(s,in_s):
    if in_s + " " in s or " " + in_s in s:
        return True

def get_address_from_certificate(text):
    """
    get the address of the company that is certified
    """
    WriteToLogs("[Info] The get_company_address function is initialized.")
    try:
        lines1 = text.splitlines()
        lines = []
        for l in lines1:
            l = re.sub("[-()#/@;:<>`+=~|.!?,]", " ", l)
            lines.append(l)
        lines[:] = [line for line in lines if line.strip()]
        key = ["Additional facilities", "Zusätzliche Einrichtungen"]
        more_address = 0
        cand_country_name = []
        cand_address = []
        cand_road = []
        exc = []
        except_key_word = ["produktion","zertifizierung","der","zertifikats","tüv","dekra","gmbh","is","tuv","tüv","dekra","gmbh", "for", "iso", "iatf", "page", "certificate", "certification", "production", "operative", "business", "contracted", "sales", "issued", "engineering", "telephone", "products", "maintenance"]
        pattern = registration_number_pattern + description_pattern
        for j in range(0, len(lines)):
            t = lines[j]
            check_type = 0
            check_str = 0
            count = 0
            li = t.split()
            # check if string only have special_character, alpha and number
            special_characters = "&—-.,ßäöüÄÖÜ"
            cks = 0
            for l in li:
                if any(c in special_characters for c in l):
                    cks = 1
                if len(l) >= 1 and l.isdigit() == True or l.isalpha() == True or cks == 1 or l.isalnum() == True:
                    count = count + 1
            if count == len(li):
                check_str = 1
            # except string have phone and fax
            ckn = 0
            li = t.split()
            for l in li:
                if l.isdigit() and len(l) > 7:
                    ckn = 1
            numbers = sum(c.isdigit() for c in t)
            # except string have except key word
            for word in except_key_word:
                hw = has_word(t.lower(),word)
                if hw == True:
                    check_type = 1
            # condition for address: have number (except dates), have road key words, have country key word 
            if has_numbers(t) == True and t.isdigit() == False and check_type == 0 and len(t) < 150 and len(t) > 10 and numbers < 12 and check_str == 1 and ckn == 0:
                if _exists_house_number_and_road(t):
                    if j not in cand_road:
                        cand_road.append(j)
                dates = _extract_dates(t)
                if dates:
                    exc.append(j)
                else:
                    for w in registration_number_pattern:
                        t_low = t.lower()
                        if w not in t_low:
                            cand_address.append(j)
                            if _exists_house_number_and_road(t):
                                if j not in cand_road:
                                    cand_road.append(j)
                        else:
                            exc.append(j)
            if _exists_country_name(t) and check_type == 0 and numbers < 10 and ckn == 0:
                for w in registration_number_pattern:
                        t_low = t.lower()
                        dates = _extract_dates(t)
                        if w not in t_low:
                            if len(t) > 15 and has_numbers(t) == True and dates == []:
                                cand_country_name.append(j)
                            if len(t) < 20 and has_numbers(t) == False and dates == []:
                                cand_country_name.append(j)
            for k in key:
                if k in t:
                    more_address = 1
            # for german certificate
            tl = t.lower()
            if "unternehmen" in tl:
                # print("unternehmen:==============")
                ind = tl.index("unternehmen")
                ind = ind + len("unternehmen") + 1
                if ind < len(tl):
                    cand_address.append(j)
                for i in range(1,7):
                    tl = lines[j+i]
                    count_str = 0
                    check_str = 0
                    li = tl.split()
                    cks = 0
                    for l in li:
                        if any(c in special_characters for c in l):
                            cks = 1
                        if len(l) >= 1 and l.isdigit() == True or l.isalpha() == True or cks == 1:
                            count_str = count_str + 1
                    if count_str == len(li):
                        check_str = 1
                    count = 0
                    for wo in pattern:
                        if wo not in lines[j+i].lower():
                            count = count + 1
                    if count == len(pattern) and check_str == 1:
                        if j+i not in cand_address:
                            cand_address.append(j+i)
                    else:
                        break
        cand = cand_country_name + cand_address + cand_road
        cand = list(set(cand))
        cand.sort()
        l_address = []
        grplist = [list(group) for group in mit.consecutive_groups(cand)]
        ger_keyword = ["der","unternehmen"]
        for k in grplist:
            s = ""
            if len(k) >= 2:
                for kk in k:
                    s = s + " " + lines[kk]
                ck = 0
                s = s.strip()
                for w in registration_number_pattern:
                    if w in s.lower():
                        ck = 1
            if len(k) == 1:
                if k[0] in cand_country_name or k[0] in cand_road:
                    if lines[k[0]] not in l_address:
                        l_address.append(lines[k[0]])
            for ger in ger_keyword:
                if ger in s.lower():
                    sl = s.lower()
                    ins = sl.index(ger) + len(ger) + 1
                    s = s[ins:]
            if ":" in s:
                s = s.replace(":","")
            if s != "" and s not in l_address and ck == 0:
                l_address.append(s)
        # delete similar string in address
        l_address = list(dedupe(l_address, threshold=90, scorer=fuzz.ratio))
        print("L_address:------------",l_address)
        WriteToLogs(f'l_address ------------------{l_address}')
        if l_address == [] or l_address == ['']:
            return None
        else:
            if more_address == 1 or len(l_address) > 1:
                final_address = []
                for add in l_address:
                    # clean address (if need)
                    add_a = add.split()
                    add_2 = ""
                    for a in add_a:
                        if len(set(a)) > 1 and a not in add_2:
                            add_2 += a + " "
                    add_2 = add_2.strip()
                    ###
                    if len(add_2) > 25 and len(add_2) < 200:
                        final_address.append(add_2)
                return final_address
            else:
                for add in l_address:
                    # clean address (if need)
                    add_a = add.split()
                    add_2 = ""
                    for a in add_a:
                        if len(set(a)) > 1 and a not in add_2:
                            add_2 += a + " "
                    add_2 = add_2.strip()
                    # # #
                    if len(add_2) > 25 and len(add_2) < 200:
                        return add_2
                # return l_address[0]   
    except Exception as exp:
        # WriteToLogs("[Error] The get_company_address function ran into an error {}".format(exp))
        return None


def get_certificate_registration_number(input_data):
    try:
        lines = input_data.splitlines()
        full_text = "".join(lines)
        full_text = "".join(full_text.split())
        exp_test = "".join("certificate no: initial certification date".split())
        exp_test_1 = "".join("certificat n :/certificate no.:".split())
        if(exp_test in full_text.lower() or exp_test_1 in full_text.lower()):
          for ind in range(0, len(lines)):
                exp_test = "".join("certificate no: initial certification date".split())
                exp_test_1 = "".join("certificat n :/certificate no.:".split())
                line_exp = "".join(lines[ind].split())
                line_exp = line_exp.lower()
                if(exp_test in line_exp or exp_test_1 in line_exp):
                  cert_line = lines[ind+1]
                  cert_line_split = cert_line.split()
                  print(cert_line_split)
                  if('date:' in cert_line_split):
                    return "".join(cert_line_split[:cert_line_split.index('date:')])
                  month_name = ['jan', 'feb', 'mar', 'apr', 'may', 'june', 'july', 'aug', 'sep', 'oct', 'nov', 'dec']
                  for word in cert_line_split:
                    for month in month_name:
                      if month in word.lower():
                        index_of_month = cert_line_split.index(word)
                        last_index_of_cert_num = index_of_month-1
                        WriteToLogs(f'Certificate Number ------------------{"".join(cert_line_split[:last_index_of_cert_num])}')
                        return "".join(cert_line_split[:last_index_of_cert_num])            
        else:
          for i in range(0,len(lines)):
            line = lines[i]
            result = registration_number_compiled_pattern.search(line)
            if result:
                original_word = lines[i]
                certificate_number = original_word[result.span()[1]+1:]
                find_certificate_word = certificate_word.search(certificate_number)
                if find_certificate_word:
                  certificate_number = certificate_number[:find_certificate_word.span()[0]]
                certificate_number = certificate_number.replace(":", '').replace('.', '').replace('|', '').strip()
                WriteToLogs(f'Certificate Number ------------------{certificate_number}')
                return certificate_number
    except Exception as err:
        WriteToLogs("get_certificate_number ran into error : {}".format(err))
        return None

def _extract_dates(s):
    """
    extracts dates from a string
    """
    months_dict =  OrderedDict([(u"january", "01"), (u"february", "02"), (u"march", "03"), (u"april", "04"), (u"may", "05"), (u"june", "06"),
                (u"july", "07"), (u"august", "08"), (u"september", "09"), (u"october", u"10"), (u"november", "11"), (u"december", "12"),
                (u"januar", "01"), (u"februar", "02"), (u"märz", "03"), (u"mai", "05"), (u"juni", "06"), 
                (u"juli", "07"), (u"oktober", "10"), (u"dezember", "12"),
                (u"jan", "01"), (u"feb", "02"), (u"mar", "03"), (u"apr", "04"), (u"aug", "08"), (u"sept", "09"), (u"oct", "10"), (u"nov", "11"), (u"dec", "12"),
                (u"sep", "09"), (u"okt", "10"), (u"dez", "12")])

    s = s.replace(u"\u2014", u"-")    # replace em dash with dash
    for item in months_dict.items():
        s = s.lower().replace(item[0], item[1])
    s = s.replace(u"th", "").replace(u"st", "").replace(u"nd", "").replace(u"rd", "")
    return re.findall(r"\d{1,4}\W+\d{1,2}\W+\d{1,4}", s)


def _get_datetime(date_s):
    """
    convert a date string to a datetime object
    """
    date_s = re.sub(r"\D", " ", date_s)
    try:
        if re.search(r"\d{4}$", date_s):
            return parse(date_s, dayfirst=True).date()
        return parse(date_s).date()
    except ValueError:
        WriteToLogs(" The _get_datetime function ran into a ValueError: {}".format(ValueError))
        return None


def _get_latest_date(dates):
    """compare several dates and get the latest one
    """
    if dates:
        latest_date = dates[0]
        for date in dates[1:]:
            if date > latest_date:
                latest_date = date
        return latest_date.isoformat()
    return None

def get_registration_date(text):
    """
    get registration date of the certificate
    """
    try:
        registration_keywords = [
            "registration",
            "valid",
            "valid from",
            "certificate issued",
            "certified since", 
            # "initial certification date", 
            "issuing date",
            "issue date",
            "issued"
            "Start Zertifizierungszyklus",
            "Datum der Erstzertifizierung",
            "Erstzertifizierung",
            "Zertifikat wirksam ist",
            "Erstmalige Zulassung",
            "Dieses Zertifikat ist gültig bis",
            "Ausgabedatum"
            ]
        registration_keywords = [word.lower() for word in registration_keywords]
        candidates = []    # save candidate dates
        lines = text.splitlines()
        lines[:] = [line for line in lines if line.strip()]
        l_key = []
        for line in lines:
            # extract dates from each line
            # print("line:  ", line)
            dates = _extract_dates(line)
            # print(" regis dates:  ", dates)
            ex_regis=["munich","nurnberg","vienna"]
            if dates:
                i = lines.index(line)
                ck = 0
                for ex in ex_regis:
                    if ex in lines[i].lower():
                        ck = 1
                if ck == 0:
                    # check whether there are registration words near candidates
                    for j in range(max(i-6, 0), min(i+6, len(lines))):
                        for word in registration_keywords:
                            if word in lines[j].lower():
                                l_key.append(word)
                                dates_in_datetime = [_get_datetime(date) for date in dates if _get_datetime(date) and _get_datetime(date) < datetime(2100, 1, 1).date()]
                                candidates += dates_in_datetime

        # get the latest date
        candidates = list(set(candidates))
        candidates.sort()
        # print("======registration date=====", candidates)
        if candidates:
            # regis_date = ""
            if len(candidates) < 3:
                regis_date = candidates[0]
                return regis_date.isoformat()
            else:
                regis_date = candidates[len(candidates)-2]
                return regis_date.isoformat()

        return None
    except Exception as exp:
        WriteToLogs("[Error] The get_registration_date function is ran into an error: {}".format(exp))
        return "Null"


def get_expiry_date(text):
    """
    get expiry date of the certificate
    """
    try:
        expiry_keywords = [
          "gültig",
          "valid",
          "until",
          "expiry",
          "expiration",
          "expire",
          "through",
          "laufzeit",
          "gültig bis",
          "gültig bis zum",
          "bis"
        ]

        candidates = []    # save candidate dates
        lines = text.splitlines()
        lines[:] = [line for line in lines if line.strip()]
        for line in lines:
            # extract dates from each line
            dates = _extract_dates(line)
            if dates:
                i = lines.index(line)
                # check whether there are expiry words near candidates
                for j in range(max(i-6, 0), min(i+6, len(lines))):
                    if any(word in lines[j].lower() for word in expiry_keywords):
                        dates_in_datetime = [_get_datetime(date) for date in dates if _get_datetime(date) and _get_datetime(date) < datetime(2100, 1, 1).date()]
                        candidates += dates_in_datetime
        # get the latest date
        if candidates:
            return _get_latest_date(candidates)

        return None
    except Exception as exp:
        WriteToLogs("[Error] The get_expiry_date function is ran into an error: {}".format(exp))
        return None

def get_certificate_description(input_data):
    WriteToLogs("--------------inside certificate description-----------------")
    description = None
    try:
        lines = input_data.splitlines()
        for i in range(0,len(lines)):
            line = lines[i].lower()
            result = description_compiled_pattern.search(line)
            if result:
                start_index = None
                if(lines[i].split()[0] == "Scope:"):
                    lines[i] = lines[i].replace("Scope:", "")
                    start_index = i
                elif(lines[i+1] == ''):
                    start_index = i+2
                else:
                    start_index = i+1
                end_index = None
                for ind in range(start_index+1, len(lines)):
                    if lines[ind] == '':
                        end_index = ind+1
                        break
                description = " ".join(lines[start_index:end_index])
                # description = " ".join(list(set([lines[start_index], description])))
                description = description.strip()
                WriteToLogs(f"description -------------------{description}")
                return description
        else:
            return None
    except Exception as err:
        WriteToLogs("get_certificate_description ran into error {}".format(err))
        return description


def certificate_content(ocr_data, ocr_address, json_file_name):
    try:
        output_format = {
	    "Filename":  "null",
        "Certificates": [
                {
                    "certificateType": "null",
                    "registrationDate": "null",
                    "expiryDate": "null",
                    "certificateNumber": "null",
                    "certificateAddress": "null",
                    "description": "null"
                }
        ],
        "Checked_on_Date": "null"
    }
        WriteToLogs("inside certificate content function...")
        recorded_on = datetime.now().isoformat()
        WriteToLogs(recorded_on)
        output_format["Checked_on_Date"] = recorded_on
        # json_file_name = json_file_name.encode("ascii", "ignore").decode()
        output_format["Filename"] = json_file_name
        result_certificate_description = get_certificate_description(ocr_data)
        if(result_certificate_description != None):
            output_format["Certificates"][0]["description"] = result_certificate_description

        result_certificate_address = get_address_from_certificate(ocr_address)
        WriteToLogs("-------------------certificate address--------------------")
        WriteToLogs(result_certificate_address)
        WriteToLogs("------------------------------------------------------------")
        if result_certificate_description != None and result_certificate_address != None:
            text_des = result_certificate_description.split(" ")
            for s in text_des:
                if s in result_certificate_address:
                    result_certificate_address = result_certificate_address.replace(s,"")
        if(result_certificate_address != None):
            output_format["Certificates"][0]["certificateAddress"] = result_certificate_address

        
        result_certificate_expiry_date = get_expiry_date(ocr_data)
        if(result_certificate_expiry_date != None):
            output_format["Certificates"][0]["expiryDate"] = result_certificate_expiry_date
        
        result_certificate_registration_date = get_registration_date(ocr_data)
        if(result_certificate_registration_date != None):
            output_format["Certificates"][0]["registrationDate"] = result_certificate_registration_date

        """Certificate Registration Number Function Call"""
        result_certificate_registration_number = get_certificate_registration_number(ocr_data)
        if(result_certificate_registration_number != None):
            output_format["Certificates"][0]["certificateNumber"] = result_certificate_registration_number
        
        result_certificate_type = get_certificate_type(ocr_data)
        if(result_certificate_type != None):
            output_format["Certificates"][0]["certificateType"] = result_certificate_type

        if result_certificate_type == None and result_certificate_registration_number == None:
            temp = json_file_name + ": " + "This is a new template"
            con_temp = []
            con_temp.append(temp)
            output_format = con_temp


    except Exception as exp:
        WriteToLogs('[Error] : DataPointExtraction class got an error in extraction_main function : {}'.format(exp))
        WriteToLogs("Exception in certificate content function...")
    
    file_name = json_file_name.replace(".pdf","")

    separate_json_output_file_name = "".join([
                                        all_separate_json,
                                        file_name,
                                        ".json"
                                        ])
    with open(separate_json_output_file_name, 'w',encoding='utf-8') as f:
        json.dump(output_format, f, default=str, indent=4, ensure_ascii=False)
    
    return output_format

def apply_threshold(img, argument):
    switcher = {
        1: cv2.threshold(cv2.GaussianBlur(img, (9, 9), 0), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1],
        2: cv2.threshold(cv2.GaussianBlur(img, (7, 7), 0), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1],
        3: cv2.threshold(cv2.GaussianBlur(img, (5, 5), 0), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1],                                                   
        18: cv2.adaptiveThreshold(cv2.medianBlur(img, 7), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2),
        19: cv2.adaptiveThreshold(cv2.medianBlur(img, 5), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2),
        20: cv2.adaptiveThreshold(cv2.medianBlur(img, 3), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2)
    }
    return switcher.get(argument, "Invalid method")

def sort_contours(cnts, method="top-to-bottom"):
	# initialize the reverse flag and sort index
	reverse = False
	i = 0
	# handle if we need to sort in reverse
	if method == "right-to-left" or method == "bottom-to-top":
		reverse = True
	# handle if we are sorting against the y-coordinate rather than
	# the x-coordinate of the bounding box
	if method == "top-to-bottom" or method == "bottom-to-top":
		i = 1
	# construct the list of bounding boxes and sort them from top to
	# bottom
	boundingBoxes = [cv2.boundingRect(c) for c in cnts]
	(cnts, boundingBoxes) = zip(*sorted(zip(cnts, boundingBoxes),
		key=lambda b:b[1][i], reverse=reverse))
	# return the list of sorted contours and bounding boxes
	return (cnts, boundingBoxes)

def convert_pdf_txt(pdf_file_path):
    document_image = []
    try: 
        pdfimage = convert_from_path(pdf_file_path,500)
    except Exception as error:
        WriteToLogs(f"Error: {error}")
        return "Not able to convert pdf to image"
    i=1
    content = []
    all_text = ""
    all_text_address = ""
    for img in pdfimage:
        page = img
        path = pdf_file_path.replace(".pdf","")
        WriteToLogs(f"path: {path}")
        path = path.replace("/home/admin/fastapi/uploads/",pdf_to_jpg_path)
        img_path = path + str(i) + '.jpg'
        WriteToLogs(f"img_path: {img_path}")
        page.save(img_path, 'JPEG')
        i +=1
        document_image.append(img_path)
        WriteToLogs(f"document image: {document_image}")
        try:
            pytesseract.pytesseract.tesseract_cmd = tesseract_path
            WriteToLogs("tesseract path read")
            # custom_config = r'-l afr+amh+ara+asm+aze+aze_cyrl+bel+ben+bod+bos+bre+bul+cat+ceb+ces+chi_sim+chi_sim_vert+chi_tra+chi_tra_vert+chr+cos+cym+dan+dan_frak+deu+deu_frak+div+dzo+ell+eng+enm+epo+equ+est+eus+fao+fas+fil+fin+fra+frk+frm+fry+gla+gle+glg+grc+guj+hat+heb+hin+hrv+hun+hye+iku+ind+isl+ita+ita_old+jav+jpn+jpn_vert+kan+kat+kat_old+kaz+khm+kir+kmr+kor+kor_vert+lao+lat+lav+lit+ltz+mal+mar+mkd+mlt+mon+mri+msa+mya+nep+nld+nor+oci+ori+osd+pan+pol+por+pus+que+ron+rus+san+sin+slk+slk_frak+slv+snd+spa+spa_old+sqi+srp+srp_latn+sun+swa+swe+syr+tam+tat+tel+tgk+tgl+tha+tir+ton+tur+uig+ukr+urd+uzb+uzb_cyrl+vie+yid+yor'
            custom_config = r'-l eng+fra+deu'
            WriteToLogs("read all the languages")
            img = cv2.imread(img_path)
            WriteToLogs("img open read")
            # image preprocessing to improve the result from OCR
            # img = cv2.resize(img, None, fx=1.5, fy=1.5, interpolation=cv2.INTER_LINEAR)
            # Convert to gray
            img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
            kernel = np.ones((1, 1), np.uint8)
            # remove some noise
            img = cv2.dilate(img, kernel, iterations=1)
            img = cv2.erode(img, kernel, iterations=1)
            # test with german character => choose method 1 or 2
            img = apply_threshold(img, 1)
            text1 = pytesseract.image_to_string(img, config=custom_config)
            WriteToLogs("extracted text using ocr")
            all_text+=text1
            WriteToLogs("text added to alltext")
            # # # bounding box text to improve address part
            raw_data = pytesseract.image_to_data(img, config=custom_config)
            img_copy = np.zeros([img.shape[0], img.shape[1]],dtype=np.uint8)
            for count, data in enumerate(raw_data.splitlines()):
                if count > 0:
                    data = data.split()
                    if len(data) == 12:
                        x, y, w, h = int(data[6]), int(data[7]), int(data[8]), int(data[9])
                        cv2.rectangle(img_copy, (x,y), (w+x, h+y), (255,255,255), -1)
            kernel = np.ones((100,100), np.uint8)
            img_dilation = cv2.dilate(img_copy, kernel, iterations=1)
            height = img_dilation.shape[1] / 10
            ch = height * 9
            contours, hierarchy = cv2.findContours(img_dilation, cv2.RETR_EXTERNAL,cv2.CHAIN_APPROX_NONE) 
            cnts, boundingBoxes = sort_contours(contours)
            for cnt in cnts:
                x, y, w, h = cv2.boundingRect(cnt)
                if y + h < ch:
                    # rect = cv2.rectangle(img, (x, y), (x + w, y + h), (0, 255, 0), 2)
                    cropped = img[y:y + h, x:x + w]
                    text = pytesseract.image_to_string(cropped, config=custom_config)
                    all_text_address += text 
            all_text_address += "\n"
            # # #
        except Exception as error:
            WriteToLogs('[Error] : Not able to convert the image to string Please refer the logs for more info : {}'.format(error))
            content.append( "Not able to convert the image to string Please refer the logs for more info")
            return content

    #encoding and decoding text to remove the unwanted characters.
    # all_text = all_text.encode("ascii", "ignore").decode()
    lang = detect(all_text)
    WriteToLogs(f"all text: {[all_text]}")
    ocr_output_file_name = path.split("/")
    json_file_name = ocr_output_file_name[-1] + ".pdf"
    ocr_output_file_name = ocr_output_file_name[-1] + ".txt"
    WriteToLogs(f"output file name: {ocr_output_file_name}")
    ocr_output_file_path = "".join([
                                ocr_output_path,
                                ocr_output_file_name
                                ])
    with open(ocr_output_file_path, 'w', encoding= 'utf-8') as file:
        file.write(all_text)
        file.close()
    cer_word = ["certificate", "certification", "zertifikat", " iso", " iatf", "certificat"]
    count_cer = 0
    for cer in cer_word:
        if cer in all_text.lower():
            # print("============cer====", cer)
            count_cer += 1
    if count_cer == 0:
        non_cer = ocr_output_file_name[1] + ": " + "This is not a certificate"
        content.append(non_cer)
        return content
    else:
        if lang == 'de' or lang == 'en':
            result_for_certificate_content = certificate_content(all_text, all_text_address, json_file_name)
            WriteToLogs("------------------------------------------------------------")
            WriteToLogs(result_for_certificate_content)
            WriteToLogs("---------------------------------------------------------------")
            return result_for_certificate_content

        else:
            content.append(f"{pdf_file_path} -- Certificate is not in English or German --  {lang}")
            return content

def create_directory(dir_name):
    try:
        if not path.exists(dir_name):
            mkdir(dir_name)
            WriteToLogs(f"Folder created  -  {dir_name}")
        else:
            WriteToLogs(f"Folder already exists  -  {dir_name}")
    except Exception as err:
        WriteToLogs(f"Exception in create directory function:  {err}")
        sys.exit("Execution stopped - Unable to create data folders")

def create_folders():
    try:
        folders_to_store = [
            pdf_to_jpg_path,
            ocr_output_path,
            all_separate_json,
            clubbed_json,
            result_csv_path,
            result_path
            ]
        for folder_name in folders_to_store:
            create_directory(folder_name)
        
        WriteToLogs("folders are created")
    except Exception as err:
        WriteToLogs(f"Error in creating folders: {err}")

def get_input_file(input_file_path):
    try:
        create_folders()
        WriteToLogs("Getting Input Files")
        WriteToLogs(input_file_path)
        response = convert_pdf_txt(input_file_path)
        WriteToLogs("--------------------------------pdf responses-------------------------------------")
        WriteToLogs(response)
        WriteToLogs("----------------------------------------------------------------------------------")
        return response
    except Exception as err:
        WriteToLogs(f"Exception in get_input_file function: {err}")
        sys.exit("Exception in get_input_file function")



    
