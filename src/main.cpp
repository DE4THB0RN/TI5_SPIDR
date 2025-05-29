#include <Arduino.h>
#include <user_interface.h>

//=================================================================================================
// Definição de constantes
//=================================================================================================
#define MAX_CANAIS = 13;

#define TYPE_MANAGEMENT 0x00
#define TYPE_CONTROL 0x01
#define TYPE_DATA 0x02
#define SUBTYPE_PROBE_REQUEST 0x04

#define DISABLE 0
#define ENABLE 1

#define CHANNEL_HOP_INTERVAL_MS 1000
static os_timer_t channelHop_timer;

//=================================================================================================
// Definições de struct
//=================================================================================================
typedef struct RxControl
{
  signed rssi : 8; // Intensidade do sinal
  unsigned rate : 4;
  unsigned is_group : 1;
  unsigned : 1;
  unsigned sig_mode : 2;
  unsigned legacy_length : 12;
  unsigned damatch0 : 1;
  unsigned damatch1 : 1;
  unsigned bssidmatch0 : 1;
  unsigned bssidmatch1 : 1;
  unsigned MCS : 7;
  unsigned CWB : 1;
  unsigned HT_length : 16;
  unsigned Smoothing : 1;
  unsigned Not_Sounding : 1;
  unsigned : 1;
  unsigned Aggregation : 1;
  unsigned STBC : 2;
  unsigned FEC_CODING : 1;
  unsigned SGI : 1;
  unsigned rxend_state : 8;
  unsigned ampdu_cnt : 8;
  unsigned channel : 4;
  unsigned : 12;
} RxControl;

typedef struct LenSeq
{
  u16 len;     // length of packet
  u16 seq;     // serial number of packet, the high 12bits are serial number, low 14 bits are Fragment number (usually be 0)
  u8 addr3[6]; // the third address in packet
} LenSeq;

struct sniffer_buf
{
  struct RxControl rx_ctrl;
  u8 buf[36];              // head of ieee80211 packet
  u16 cnt;                 // number count of packet
  struct LenSeq lenseq[1]; // length of packet
};

typedef struct sniffer_buf2
{
  RxControl wifi_ctrl;
  u8 buf[112]; // may be 240, please refer to the real source code
  u16 cnt;
  u16 len; // length of packet
} sniffer_buf2;

typedef struct cliente
{
  uint8_t bssid[6];
  uint8_t station[6];
  uint8_t ap[6];
  int canal;
  int err;
  signed rssi;
  uint16_t seq_n;
} cliente;

typedef struct beacon
{
  uint8_t bssid[6];
  uint8_t ssid[33];
  int ssid_len;
  int canal;
  int err;
  signed rssi;
  uint8_t capa[2];
} beacon;
//=================================================================================================
//=================================================================================================
// Definição de métodos
//=================================================================================================
static void ICACHE_FLASH_ATTR promiscuous_handler(uint8_t *buffer, uint16_t length);
String lerMAC(uint8_t MAC[6]);
void pularCanal();
cliente ler_probe(uint8_t *quadro, uint16_t len, signed rssi);
cliente ler_dados(uint8_t *quadro, uint16_t len, signed rssi, unsigned canal);
beacon ler_beacon(uint8_t *quadro, uint16_t len, signed rssi);
void printarCliente(cliente cli);
void printarBeacon(beacon be);
//=================================================================================================
//=================================================================================================
// Métodos para as structs
//=================================================================================================

cliente ler_probe(uint8_t *quadro, uint16_t len, signed rssi)
{
  cliente cli;
  cli.canal = -1;
  cli.err = 0;
  cli.rssi = rssi;
  memset(cli.bssid, 0xFF, 6);
  memcpy(cli.station, quadro + 10, 6);
  if ((cli.station[0] & 2) == 2)
    cli.canal = -2; // MAC aleatório fazendo gracinha
  return cli;
}

cliente ler_dados(uint8_t *quadro, uint16_t len, signed rssi, unsigned canal)
{
  uint8_t broadcast1[3] = {0x01, 0x00, 0x5e};
  uint8_t broadcast2[6] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
  uint8_t broadcast3[3] = {0x33, 0x33, 0x00};

  cliente cli;
  cli.canal = canal;
  cli.err = 0;
  cli.rssi = rssi;
  uint8_t *bssid;
  uint8_t *station;
  uint8_t *ap;
  uint8_t ds;

  ds = quadro[1] & 3;
  switch (ds)
  {
  case 0:
    bssid = quadro + 16;
    station = quadro + 10;
    ap = quadro + 4;
    break;
  case 1:
    bssid = quadro + 4;
    station = quadro + 10;
    ap = quadro + 16;
    break;
  case 2:
    bssid = quadro + 10;
    if (memcmp(quadro + 4, broadcast1, 3) || memcmp(quadro + 4, broadcast2, 3) || memcmp(quadro + 4, broadcast3, 3))
    {
      station = quadro + 16;
      ap = quadro + 4;
    }
    else
    {
      station = quadro + 4;
      ap = quadro + 16;
    }
    break;
  case 3:
    bssid = quadro + 10;
    station = quadro + 4;
    ap = quadro + 4;
    break;
  }

  memcpy(cli.station, station, 6);
  memcpy(cli.bssid, bssid, 6);
  memcpy(cli.ap, ap, 6);

  cli.seq_n = quadro[23] * 0xFF + (quadro[22] & 0xF0);

  return cli;
}

beacon ler_beacon(uint8_t *quadro, uint16_t len, signed rssi)
{
  beacon be;
  be.ssid_len = 0;
  be.canal = 0;
  be.err = 0;
  be.rssi = rssi;
  int pos = 36;

  if (quadro[pos] == 0x00)
  {
    while (pos < len && pos > 0)
    {
      switch (quadro[pos])
      {
      case 0x00:
        be.ssid_len = (int)quadro[pos + 1];
        if (be.ssid_len == 0)
        {
          memset(be.ssid, '\x00', 33);
          break;
        }
        if (be.ssid_len < 0)
        {
          be.err = -1;
          break;
        }
        if (be.ssid_len > 32)
        {
          be.err = -2;
          break;
        }
        memset(be.ssid, '\x00', 33);
        memcpy(be.ssid, quadro + pos + 2, be.ssid_len);
        be.err = 0;
        break;
      case 0x03:
        be.canal = (int)quadro[pos + 2];
        pos = -1;
        break;
      }
      pos += (int)quadro[pos + 1] + 2;
    }
  }
  else
  {
    be.err = -3;
  }

  be.capa[0] = quadro[34];
  be.capa[1] = quadro[35];
  memcpy(be.bssid, quadro + 10, 16);

  return be;
}

void printarCliente(cliente cli)
{
  if (cli.err == 0)
  {
    Serial.printf("Cliente: ");
    Serial.print(lerMAC(cli.station));
    Serial.printf(" -> ");
    Serial.print(lerMAC(cli.ap));
    Serial.printf("    RSSI: %2d     Canal: %d\n", cli.rssi, cli.canal);
  }
}

void printarBeacon(beacon be)
{
  if (be.err == 0)
  {
    Serial.printf("Beacon: ");
    Serial.print(lerMAC(be.bssid));
    Serial.printf("    RSSI: %2d     Canal: %d\n", be.rssi, be.canal);
  }
}

//=================================================================================================
// Métodos de utilidade
//=================================================================================================

String lerMAC(uint8_t MAC[6])
{
  String resp = "";
  for (int i = 0; i < 6; i++)
  {
    if (MAC[i] < 16)
      resp = resp + "0" + String(MAC[i], HEX);
    else
      resp += String(MAC[i], HEX);
    if (i < 5)
      resp += ":";
  }
  return resp;
}

//=================================================================================================

//=================================================================================================
// Métodos para a checagem dos pacotes
//=================================================================================================

static void ICACHE_FLASH_ATTR promiscuous_handler(uint8_t *buffer, uint16_t length)
{

  if (length == 12)
  {
    RxControl *wifi_ctrl = (RxControl *)buffer;
  }
  else if (length == 128)
  {
    sniffer_buf2 *sniffer = (sniffer_buf2 *)buffer;
    if (sniffer->buf[0] == 0x80)
    {
      beacon b_info = ler_beacon(sniffer->buf, 112, sniffer->wifi_ctrl.rssi);
      if (b_info.rssi > -70)
        printarBeacon(b_info);
    }
    else if (sniffer->buf[0] == 0x40)
    {
      cliente c_info = ler_probe(sniffer->buf, 36, sniffer->wifi_ctrl.rssi);
      if (c_info.rssi > -70)
        printarCliente(c_info);
    }
  }
  else
  {
    sniffer_buf *sniffer = (sniffer_buf *)buffer;
    if ((sniffer->buf[0] == 0x08) || (sniffer->buf[0] == 0x88))
    {
      cliente c_info = ler_dados(sniffer->buf, 36, sniffer->rx_ctrl.rssi, sniffer->rx_ctrl.channel);
      if (c_info.rssi > -70)
        printarCliente(c_info);
    }
  }
}

void pularCanal()
{
  // Pular do canal 1 ao 13
  // O 14 só existe no Japão
  uint8 new_channel = wifi_get_channel() + 1;
  if (new_channel > 13)
  {
    new_channel = 1;
  }
  wifi_set_channel(new_channel);
}

//=================================================================================================

//=================================================================================================
// Métodos comuns
//=================================================================================================

void setup()
{

  Serial.begin(115200);
  delay(10);
  wifi_set_opmode(STATION_MODE);
  wifi_set_channel(1);
  wifi_promiscuous_enable(DISABLE);
  delay(10);
  wifi_set_promiscuous_rx_cb(promiscuous_handler);
  delay(10);
  wifi_promiscuous_enable(ENABLE);

  os_timer_disarm(&channelHop_timer);
  os_timer_setfn(&channelHop_timer, (os_timer_func_t *)pularCanal, NULL);
  os_timer_arm(&channelHop_timer, CHANNEL_HOP_INTERVAL_MS, 1);
}

void loop()
{
  delay(10);
}

//=================================================================================================