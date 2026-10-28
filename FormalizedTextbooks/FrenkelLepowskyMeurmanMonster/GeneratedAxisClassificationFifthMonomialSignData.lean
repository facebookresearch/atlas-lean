/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignCorrection

/-! Checked source-code translations and Pauli phases for the twelve actual Golay sign lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The twelve genuine source Golay basis codes. -/
def generatedFifthSignCode : Fin 12 → Fin 4096 :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- Actual output dictionary labels for the original Y states. -/
def generatedFifthSignOutput : Fin 12 → Fin 64 → Fin 2048 :=
  ![
  ![1720, 1718, 1726, 1712, 1970, 1980, 1982, 1968, 1725, 1715, 1723, 1717, 1975, 1977, 1979, 1973,
    1794, 1804, 1796, 1802, 1544, 1542, 1540, 1546, 1805, 1795, 1803, 1797, 1543, 1545, 1547, 1541,
    1153, 1162, 1333, 1328, 1338, 1343, 1152, 1163, 1413, 1422, 1073, 1076, 1086, 1083, 1412, 1423,
    1411, 1416, 1079, 1074, 1080, 1085, 1410, 1417, 1161, 1154, 1341, 1336, 1330, 1335, 1160, 1155],
  ![1723, 1717, 1725, 1715, 1969, 1983, 1981, 1971, 1726, 1712, 1720, 1718, 1972, 1978, 1976, 1974,
    1793, 1807, 1799, 1801, 1547, 1541, 1543, 1545, 1806, 1792, 1800, 1798, 1540, 1546, 1544, 1542,
    1154, 1161, 1334, 1331, 1337, 1340, 1155, 1160, 1414, 1421, 1074, 1079, 1085, 1080, 1415, 1420,
    1408, 1419, 1076, 1073, 1083, 1086, 1409, 1418, 1162, 1153, 1342, 1339, 1329, 1332, 1163, 1152],
  ![1725, 1715, 1723, 1717, 1975, 1977, 1979, 1973, 1720, 1718, 1726, 1712, 1970, 1980, 1982, 1968,
    1799, 1801, 1793, 1807, 1549, 1539, 1537, 1551, 1800, 1798, 1806, 1792, 1538, 1548, 1550, 1536,
    1156, 1167, 1328, 1333, 1343, 1338, 1157, 1166, 1408, 1419, 1076, 1073, 1083, 1086, 1409, 1418,
    1414, 1421, 1074, 1079, 1085, 1080, 1415, 1420, 1164, 1159, 1336, 1341, 1335, 1330, 1165, 1158],
  ![1713, 1727, 1719, 1721, 1979, 1973, 1975, 1977, 1716, 1722, 1714, 1724, 1982, 1968, 1970, 1980,
    1803, 1797, 1805, 1795, 1537, 1551, 1549, 1539, 1796, 1802, 1794, 1804, 1550, 1536, 1538, 1548,
    1160, 1155, 1340, 1337, 1331, 1334, 1161, 1154, 1420, 1415, 1080, 1085, 1079, 1074, 1421, 1414,
    1418, 1409, 1086, 1083, 1073, 1076, 1419, 1408, 1152, 1163, 1332, 1329, 1339, 1342, 1153, 1162],
  ![1705, 1703, 1711, 1697, 1955, 1965, 1967, 1953, 1708, 1698, 1706, 1700, 1958, 1960, 1962, 1956,
    1811, 1821, 1813, 1819, 1561, 1559, 1557, 1563, 1820, 1810, 1818, 1812, 1558, 1560, 1562, 1556,
    1168, 1179, 1316, 1313, 1323, 1326, 1169, 1178, 1428, 1439, 1056, 1061, 1071, 1066, 1429, 1438,
    1426, 1433, 1062, 1059, 1065, 1068, 1427, 1432, 1176, 1171, 1324, 1321, 1315, 1318, 1177, 1170],
  ![1689, 1687, 1695, 1681, 1939, 1949, 1951, 1937, 1692, 1682, 1690, 1684, 1942, 1944, 1946, 1940,
    1827, 1837, 1829, 1835, 1577, 1575, 1573, 1579, 1836, 1826, 1834, 1828, 1574, 1576, 1578, 1572,
    1184, 1195, 1300, 1297, 1307, 1310, 1185, 1194, 1444, 1455, 1040, 1045, 1055, 1050, 1445, 1454,
    1442, 1449, 1046, 1043, 1049, 1052, 1443, 1448, 1192, 1187, 1308, 1305, 1299, 1302, 1193, 1186],
  ![1785, 1783, 1791, 1777, 2035, 2045, 2047, 2033, 1788, 1778, 1786, 1780, 2038, 2040, 2042, 2036,
    1859, 1869, 1861, 1867, 1609, 1607, 1605, 1611, 1868, 1858, 1866, 1860, 1606, 1608, 1610, 1604,
    1216, 1227, 1396, 1393, 1403, 1406, 1217, 1226, 1476, 1487, 1136, 1141, 1151, 1146, 1477, 1486,
    1474, 1481, 1142, 1139, 1145, 1148, 1475, 1480, 1224, 1219, 1404, 1401, 1395, 1398, 1225, 1218],
  ![1593, 1591, 1599, 1585, 1843, 1853, 1855, 1841, 1596, 1586, 1594, 1588, 1846, 1848, 1850, 1844,
    1923, 1933, 1925, 1931, 1673, 1671, 1669, 1675, 1932, 1922, 1930, 1924, 1670, 1672, 1674, 1668,
    1024, 1035, 1460, 1457, 1467, 1470, 1025, 1034, 1284, 1295, 1200, 1205, 1215, 1210, 1285, 1294,
    1282, 1289, 1206, 1203, 1209, 1212, 1283, 1288, 1032, 1027, 1468, 1465, 1459, 1462, 1033, 1026],
  ![1977, 1975, 1983, 1969, 1715, 1725, 1727, 1713, 1980, 1970, 1978, 1972, 1718, 1720, 1722, 1716,
    1539, 1549, 1541, 1547, 1801, 1799, 1797, 1803, 1548, 1538, 1546, 1540, 1798, 1800, 1802, 1796,
    1408, 1419, 1076, 1073, 1083, 1086, 1409, 1418, 1156, 1167, 1328, 1333, 1343, 1338, 1157, 1166,
    1154, 1161, 1334, 1331, 1337, 1340, 1155, 1160, 1416, 1411, 1084, 1081, 1075, 1078, 1417, 1410],
  ![1209, 1207, 1215, 1201, 1459, 1469, 1471, 1457, 1212, 1202, 1210, 1204, 1462, 1464, 1466, 1460,
    1283, 1293, 1285, 1291, 1033, 1031, 1029, 1035, 1292, 1282, 1290, 1284, 1030, 1032, 1034, 1028,
    1664, 1675, 1844, 1841, 1851, 1854, 1665, 1674, 1924, 1935, 1584, 1589, 1599, 1594, 1925, 1934,
    1922, 1929, 1590, 1587, 1593, 1596, 1923, 1928, 1672, 1667, 1852, 1849, 1843, 1846, 1673, 1666],
  ![697, 695, 703, 689, 947, 957, 959, 945, 700, 690, 698, 692, 950, 952, 954, 948,
    771, 781, 773, 779, 521, 519, 517, 523, 780, 770, 778, 772, 518, 520, 522, 516,
    128, 139, 308, 305, 315, 318, 129, 138, 388, 399, 48, 53, 63, 58, 389, 398,
    386, 393, 54, 51, 57, 60, 387, 392, 136, 131, 316, 313, 307, 310, 137, 130],
  ![1721, 1719, 1727, 1713, 1971, 1981, 1983, 1969, 1724, 1714, 1722, 1716, 1974, 1976, 1978, 1972,
    1795, 1805, 1797, 1803, 1545, 1543, 1541, 1547, 1804, 1794, 1802, 1796, 1542, 1544, 1546, 1540,
    1152, 1163, 1332, 1329, 1339, 1342, 1153, 1162, 1412, 1423, 1072, 1077, 1087, 1082, 1413, 1422,
    1410, 1417, 1078, 1075, 1081, 1084, 1411, 1416, 1160, 1155, 1340, 1337, 1331, 1334, 1161, 1154]]

/-- Pauli modulation masks solving the full original Y-state phase equations. -/
def generatedFifthSignModulation : Fin 12 → Fin 4096 :=
  ![512, 128, 512, 128, 774, 268, 778, 512, 0, 527, 143, 0]

/-- The original central correction bits. -/
def generatedFifthSignCentral : Fin 12 → ZMod 2 :=
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]

/-- The actual Q correction, retaining translation, modulation and central coefficient. -/
def generatedFifthSignCorrection (k : Fin 12) : Q :=
  generatedAxisFourthQFromSpin (golayLabelCoefficients (generatedFifthSignCode k))
    (golayLabelCoefficients (generatedFifthSignModulation k)) (generatedFifthSignCentral k)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every low-spin translation against the actual source Golay coefficient vectors.
/-- Each source word has the displayed genuine two-representative dictionary transport. -/
theorem generatedFifth_sign_output_translation : ∀ k : Fin 12, ∀ j : Fin 64,
    generatedFifthSpinLow (generatedFifthSignOutput k j) +
      golayLabelCoefficients (generatedFifthSignCode k) =
        generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
          (if k = 11 then (1 : ZMod 2) else 0) • (Pi.single 11 1 : SpinIndex) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check the reverse translation for each actual correcting Pauli operator.
/-- Each correcting translation restores the original dictionary row. -/
theorem generatedFifth_sign_correction_translation : ∀ k : Fin 12, ∀ j : Fin 64,
    generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
      spinTranslation (generatedFifthSignCorrection k) =
        generatedFifthSpinLow (generatedFifthSignOutput k j) +
          (if k = 11 then (1 : ZMod 2) else 0) • (Pi.single 11 1 : SpinIndex) := by
  decide +kernel

/-- Every correction has equal phase on the two genuine spin representatives. -/
theorem generatedFifth_sign_correction_omega : ∀ k : Fin 12,
    spinDot (spinModulation (generatedFifthSignCorrection k)) (Pi.single 11 1) = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check all 768 original source phases and their correcting full Pauli characters.
/-- Every original source Y-state phase is exactly canceled by the actual correcting Q. -/
theorem generatedFifth_sign_correction_phase : ∀ k : Fin 12, ∀ j : Fin 64,
    spinPhase (generatedFifthSignCorrection k)
      (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1) +
      spinTranslation (generatedFifthSignCorrection k) 11 +
      generatedFifthYMaskPhase (generatedFifthSignOutput k j)
        (generatedFifthOddRootOutputData j).2 =
      generatedFifthSignDictionaryPhase (sourceQCode (generatedFifthSignCode k) 0)
        (generatedFifthOddRootOutputData j).1 (generatedFifthSignOutput k j) +
      generatedFifthYMaskPhase (generatedFifthOddRootOutputData j).1
        (generatedFifthOddRootOutputData j).2 := by
  unfold generatedFifthSignDictionaryPhase
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
