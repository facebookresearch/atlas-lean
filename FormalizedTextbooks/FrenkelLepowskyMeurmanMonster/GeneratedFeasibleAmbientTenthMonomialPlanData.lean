/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWordData

/-! Complete Parker-phase plans for the five nonempty monomial words of the actual root-two
normalization of the Fifth axis (the Tenth middle vector). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every intermediate coordinate and phase model for root-two stage 0. -/
def generatedFeasibleAmbientTenthMonomialPlan00 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![241, 1075, 355, 659, 1040, 48, 1152, 192, 779, 12, 1265, 3069]
        ![1038, 14, 1032, 1032, 880, 928, 960, 896, 1536, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![775, 779, 1453, 1629, 808, 841, 1039, 1038, 1075, 1218, 1793, 3069]
        ![184, 108, 1128, 1128, 656, 1376, 1536, 256, 0, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![871, 1900, 889, 1000, 1065, 97, 783, 1, 1696, 1008, 1126, 2971]
        ![2016, 2032, 4, 1888, 896, 32, 64, 768, 1792, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1057, 1061, 453, 979, 79, 1096, 1127, 782, 691, 145, 71, 2683]
        ![2047, 948, 1972, 832, 1408, 1088, 704, 1280, 768, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![546, 691, 336, 838, 1753, 1744, 252, 923, 1061, 4, 593, 2683]
        ![2029, 934, 1964, 2032, 1824, 1728, 1536, 1152, 1536, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![332, 713, 664, 1495, 1160, 9, 458, 871, 2038, 534, 797, 3328]
        ![759, 250, 376, 1688, 656, 1088, 576, 1024, 1792, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1888, 1049, 1456, 1660, 1941, 1153, 122, 685, 946, 1871, 1149, 2255]
        ![826, 308, 1984, 1152, 960, 1856, 448, 1024, 256, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1277, 946, 390, 586, 62, 177, 2007, 1691, 1049, 889, 1969, 2255]
        ![748, 930, 540, 1072, 1072, 1312, 128, 768, 1024, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![727, 664, 713, 432, 882, 963, 512, 1179, 10, 1516, 844, 2733]
        ![1240, 906, 404, 680, 1760, 1408, 1984, 128, 512, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1423, 1359, 263, 1259, 745, 298, 1792, 923, 1059, 2, 411, 2487]
        ![748, 4, 1404, 696, 176, 1088, 1472, 1408, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1854, 1871, 781, 783, 1789, 2007, 143, 788, 1582, 371, 1044, 2919]
        ![1373, 1108, 1708, 944, 432, 64, 192, 1280, 1536, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1885, 1582, 527, 525, 1948, 1744, 491, 534, 1871, 113, 1046, 2919]
        ![1985, 318, 404, 952, 176, 1408, 1024, 1024, 1280, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![923, 46, 79, 62, 1239, 519, 182, 672, 779, 1999, 843, 2191]
        ![824, 1068, 248, 216, 1984, 512, 256, 256, 1280, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1220, 779, 1077, 1092, 2034, 8, 1510, 1754, 46, 949, 826, 2191]
        ![725, 1390, 224, 688, 1472, 416, 320, 1024, 768, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![2, 783, 527, 1362, 1224, 2042, 1504, 828, 16, 113, 824, 2919]
        ![259, 14, 504, 424, 1408, 320, 768, 256, 512, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![97, 16, 371, 1582, 2007, 1789, 1156, 64, 783, 781, 1125, 2919]
        ![1220, 752, 1544, 1592, 352, 800, 0, 512, 512, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1756, 1077, 779, 6, 979, 1326, 192, 128, 1652, 1940, 1028, 2539]
        ![1009, 1858, 612, 344, 608, 320, 192, 1792, 1792, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![480, 1652, 1654, 1403, 402, 1117, 1679, 1533, 1077, 745, 1801, 2539]
        ![467, 1452, 0, 824, 16, 768, 320, 512, 0, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![64, 1152, 177, 600, 1915, 806, 1435, 102, 1035, 1702, 1769, 2127]
        ![488, 1794, 740, 488, 832, 1408, 832, 1536, 1280, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![685, 1035, 727, 62, 2032, 1360, 256, 512, 1152, 1216, 1024, 2127]
        ![1072, 1698, 4, 1752, 496, 928, 448, 896, 1280, 1536, 1024, 0])
  ]

/-- Every intermediate coordinate and phase model for root-two stage 1. -/
def generatedFeasibleAmbientTenthMonomialPlan01 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![241, 1075, 355, 659, 1040, 48, 1152, 192, 779, 12, 1265, 3069]
        ![1038, 14, 1032, 1032, 880, 928, 960, 896, 1536, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![775, 779, 1453, 1629, 808, 841, 1039, 1038, 1075, 1218, 1793, 3069]
        ![184, 108, 1128, 1128, 656, 1376, 1536, 256, 0, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1088, 4, 2, 1216, 1838, 1127, 1031, 9, 393, 1342, 1030, 2191]
        ![528, 1732, 1728, 208, 80, 192, 1344, 1920, 0, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1207, 393, 376, 1466, 1699, 458, 349, 371, 4, 1092, 196, 2191]
        ![836, 164, 932, 1888, 1840, 800, 1984, 896, 1792, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1008, 659, 1453, 1706, 1639, 1897, 439, 46, 1220, 1218, 820, 3069]
        ![1327, 570, 1480, 984, 288, 608, 192, 384, 1792, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![6, 1220, 12, 779, 48, 1040, 312, 1423, 659, 355, 51, 3069]
        ![1825, 1250, 788, 800, 1776, 832, 576, 1280, 256, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![409, 376, 393, 234, 5, 1045, 1154, 269, 122, 738, 53, 2048]
        ![1731, 1204, 736, 976, 1168, 544, 320, 1536, 512, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1153, 64, 546, 192, 425, 1468, 1059, 1326, 1239, 172, 428, 3840]
        ![1228, 26, 408, 344, 112, 1504, 1024, 256, 256, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1147, 1239, 1615, 1197, 1342, 1077, 1360, 323, 64, 1217, 846, 3840]
        ![1746, 1136, 0, 176, 1120, 224, 320, 1152, 256, 1024, 0, 0])
  ]

/-- Every intermediate coordinate and phase model for root-two stage 2. -/
def generatedFeasibleAmbientTenthMonomialPlan02 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
        ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![209, 1218, 1743, 692, 177, 1152, 1056, 97, 828, 332, 1184, 3079]
        ![1085, 1696, 1236, 520, 1312, 1440, 1920, 0, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1072, 3, 1753, 1941, 1216, 64, 48, 81, 652, 534, 1137, 3328]
        ![1281, 450, 724, 1880, 592, 352, 384, 768, 1536, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![154, 652, 252, 432, 1615, 1679, 597, 1652, 3, 1075, 1341, 3328]
        ![879, 1198, 1244, 216, 1536, 1568, 0, 128, 1024, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![97, 453, 1059, 16, 1000, 1383, 390, 2034, 1465, 1038, 1447, 2078]
        ![612, 234, 1420, 1080, 560, 864, 448, 1408, 1024, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![439, 1465, 393, 1466, 1940, 1435, 172, 600, 453, 420, 404, 2078]
        ![762, 1784, 664, 352, 288, 1760, 896, 1920, 512, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1652, 1653, 912, 564, 1975, 556, 727, 143, 371, 643, 35, 3069]
        ![1587, 1504, 268, 1704, 528, 960, 512, 1920, 1536, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1239, 1753, 761, 122, 480, 972, 1039, 1152, 1629, 1370, 1623, 3085]
        ![1234, 210, 2044, 376, 656, 1440, 64, 256, 1792, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![775, 1629, 1453, 1838, 356, 92, 79, 980, 1753, 526, 1236, 3085]
        ![1334, 308, 24, 1696, 288, 64, 128, 896, 1024, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![420, 182, 912, 1508, 1456, 312, 1792, 923, 1699, 643, 1392, 3069]
        ![6, 980, 1768, 368, 816, 1568, 0, 128, 1536, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![439, 234, 393, 1466, 192, 1160, 1771, 1179, 214, 1652, 1223, 2078]
        ![1598, 574, 1404, 360, 1168, 384, 1024, 1536, 256, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1698, 214, 1696, 659, 252, 1888, 534, 946, 234, 349, 244, 2078]
        ![675, 318, 1436, 120, 1168, 1184, 384, 1792, 512, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![154, 284, 1000, 1127, 8, 1948, 838, 420, 1360, 1075, 110, 3328]
        ![1188, 1590, 1072, 1288, 448, 736, 1984, 256, 768, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![355, 1360, 1629, 466, 1092, 1936, 691, 1041, 284, 390, 2017, 3328]
        ![1310, 984, 272, 520, 1008, 704, 896, 1280, 1792, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![738, 1696, 214, 336, 710, 1366, 32, 1073, 1897, 871, 1666, 2539]
        ![104, 1902, 876, 1128, 480, 1920, 1024, 640, 512, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1038, 1897, 2035, 1653, 783, 779, 145, 788, 1696, 1090, 1796, 2539]
        ![545, 1132, 624, 2024, 656, 0, 64, 128, 1792, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1935, 1127, 1629, 1854, 1035, 4, 1040, 901, 2032, 390, 139, 3328]
        ![1879, 1588, 1888, 0, 128, 1248, 1536, 128, 1280, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1654, 2032, 1075, 1360, 1948, 8, 1509, 491, 1127, 1000, 488, 3328]
        ![922, 1944, 2044, 16, 16, 1920, 1088, 768, 768, 512, 0, 0])
  ]

/-- Every intermediate coordinate and phase model for root-two stage 3. -/
def generatedFeasibleAmbientTenthMonomialPlan03 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
        ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1008, 1629, 355, 402, 1310, 81, 1679, 161, 10, 12, 2044, 3069]
        ![1855, 242, 1796, 1792, 368, 672, 448, 640, 1792, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![145, 1822, 889, 30, 738, 1359, 1885, 1582, 1081, 241, 1901, 2971]
        ![292, 2032, 240, 1128, 112, 1504, 1664, 0, 768, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1224, 1081, 1031, 1888, 453, 1259, 672, 336, 1822, 1935, 1034, 2971]
        ![1072, 336, 1728, 1592, 1920, 224, 1792, 640, 1024, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![534, 469, 420, 2027, 1487, 1326, 1370, 1008, 1792, 871, 1564, 2683]
        ![785, 1378, 784, 1376, 944, 1920, 1216, 640, 1024, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1117, 1342, 1207, 1691, 979, 225, 1516, 1706, 79, 1615, 577, 3086]
        ![118, 986, 1496, 1336, 16, 224, 384, 0, 512, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1536, 79, 923, 439, 1698, 1216, 912, 390, 1342, 355, 109, 3086]
        ![817, 388, 1120, 984, 64, 608, 960, 640, 1024, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1652, 1088, 1057, 8, 1743, 610, 491, 534, 933, 556, 1561, 3083]
        ![103, 984, 2036, 360, 96, 224, 448, 128, 512, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![292, 128, 536, 1217, 214, 1197, 1039, 1021, 949, 1065, 1853, 2191]
        ![930, 984, 8, 1800, 1984, 800, 1920, 1024, 1024, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1948, 949, 1941, 332, 995, 1566, 4, 1648, 128, 420, 484, 2191]
        ![1563, 764, 836, 528, 624, 1152, 640, 0, 1024, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![2034, 1057, 1088, 1508, 1435, 901, 12, 1660, 1999, 376, 1656, 2048]
        ![1869, 848, 248, 272, 176, 1216, 960, 1408, 0, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1719, 1999, 1771, 1871, 1653, 1040, 1756, 1239, 1057, 979, 2012, 2048]
        ![570, 764, 1992, 1384, 640, 512, 192, 1792, 256, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1753, 1217, 1941, 9, 425, 613, 779, 523, 453, 420, 261, 2191]
        ![713, 848, 1168, 1640, 64, 800, 64, 768, 1024, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1045, 209, 691, 30, 172, 972, 782, 256, 624, 1948, 1296, 2919]
        ![1281, 414, 1284, 880, 272, 960, 704, 512, 1280, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1516, 624, 491, 838, 525, 1466, 1153, 600, 209, 1220, 1981, 2919]
        ![1593, 1148, 580, 16, 1312, 640, 320, 1792, 0, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![526, 1941, 1217, 5, 92, 1510, 1160, 1744, 1310, 81, 593, 3840]
        ![1823, 860, 1156, 792, 1312, 352, 1600, 640, 256, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1359, 1310, 267, 1487, 727, 1037, 546, 794, 1941, 1435, 1685, 3840]
        ![1574, 1746, 1724, 1048, 1696, 480, 640, 384, 768, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![685, 30, 491, 1031, 1090, 1754, 1423, 312, 1936, 1220, 1080, 2919]
        ![965, 498, 1848, 1808, 1696, 512, 1600, 896, 1792, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![852, 1936, 1948, 624, 972, 172, 512, 1871, 30, 691, 468, 2919]
        ![1746, 82, 1084, 48, 640, 1824, 128, 1664, 1536, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1207, 267, 1310, 1965, 332, 480, 1999, 128, 1039, 1536, 640, 2191]
        ![877, 1886, 816, 0, 816, 1984, 1216, 1280, 1536, 1536, 0, 0])
  ]

/-- Every intermediate coordinate and phase model for root-two stage 4. -/
def generatedFeasibleAmbientTenthMonomialPlan04 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
        ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![209, 1218, 1743, 692, 177, 1152, 1056, 97, 828, 332, 1184, 3079]
        ![1085, 1696, 1236, 520, 1312, 1440, 1920, 0, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1072, 3, 1753, 1941, 1216, 64, 48, 81, 652, 534, 1137, 3328]
        ![1281, 450, 724, 1880, 592, 352, 384, 768, 1536, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![154, 652, 252, 432, 1615, 1679, 597, 1652, 3, 1075, 1341, 3328]
        ![879, 1198, 1244, 216, 1536, 1568, 0, 128, 1024, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![97, 453, 1059, 16, 1000, 1383, 390, 2034, 1465, 1038, 1447, 2078]
        ![612, 234, 1420, 1080, 560, 864, 448, 1408, 1024, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![756, 912, 1653, 635, 1582, 841, 946, 1088, 1468, 794, 1478, 2775]
        ![675, 538, 836, 720, 240, 960, 1344, 384, 1024, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1702, 1468, 1035, 5, 2, 1898, 963, 1598, 912, 356, 456, 2775]
        ![628, 150, 16, 496, 1952, 1824, 1088, 1408, 1024, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1075, 1466, 1059, 1090, 458, 1896, 2038, 1533, 491, 1038, 1531, 2078]
        ![691, 568, 652, 832, 368, 1920, 1152, 384, 1024, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1509, 491, 420, 453, 1435, 1940, 1756, 122, 1466, 393, 1434, 2078]
        ![1704, 1324, 1376, 656, 880, 1696, 1920, 896, 1536, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![523, 1035, 1468, 1077, 1508, 624, 1753, 1699, 781, 1154, 127, 3069]
        ![997, 228, 212, 1400, 1776, 1984, 192, 384, 1024, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1935, 781, 1854, 1719, 738, 980, 761, 1057, 1035, 1536, 502, 3069]
        ![1787, 288, 1280, 1768, 736, 1760, 1984, 1920, 512, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![122, 1754, 727, 1239, 1179, 1871, 161, 1152, 1648, 12, 1657, 3086]
        ![366, 14, 664, 1584, 1056, 1952, 1728, 384, 1280, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![949, 1059, 1061, 1065, 664, 1495, 546, 1698, 692, 1915, 1539, 2487]
        ![12, 130, 1612, 1736, 0, 32, 64, 128, 256, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![192, 1154, 756, 1423, 1838, 761, 310, 1940, 936, 209, 1462, 3584]
        ![1445, 908, 1584, 168, 1376, 1568, 1152, 512, 512, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![889, 936, 1639, 284, 4, 1756, 1706, 775, 1154, 1090, 717, 3584]
        ![545, 502, 1700, 192, 1776, 1344, 1472, 768, 1792, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![12, 1220, 1061, 1936, 713, 1752, 458, 1453, 269, 1915, 705, 2487]
        ![843, 322, 1752, 616, 1856, 1952, 704, 1536, 256, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1654, 269, 1942, 1059, 1792, 1039, 1383, 1566, 1220, 1224, 372, 2487]
        ![1567, 496, 292, 968, 352, 544, 1920, 1408, 1792, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1536, 1280, 727, 685, 1652, 783, 1898, 889, 852, 949, 1908, 3086]
        ![580, 238, 1120, 952, 1056, 1152, 192, 1792, 1280, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![225, 852, 610, 536, 32, 1854, 1466, 972, 1280, 768, 1806, 3086]
        ![801, 1954, 1428, 728, 512, 512, 1792, 128, 1280, 1024, 1024, 0])
  ]

/-- The five checked root-two plans. -/
def generatedFeasibleAmbientTenthMonomialPlan : Fin 5 → RepresentativeSpinPlan (Fin 2 × Bool) :=
  ![generatedFeasibleAmbientTenthMonomialPlan00, generatedFeasibleAmbientTenthMonomialPlan01,
      generatedFeasibleAmbientTenthMonomialPlan02, generatedFeasibleAmbientTenthMonomialPlan03,
      generatedFeasibleAmbientTenthMonomialPlan04]

/-- The literal root-two monomial words, in actual product order. -/
def generatedFeasibleAmbientTenthMonomialWord (k : Fin 5) : List (Fin 2 × Bool) :=
  (generatedFeasibleAmbientTenthMonomialPlan k).map Prod.fst

/-- The final signed coordinate model of each root-two word. -/
def generatedFeasibleAmbientTenthMonomialModel (k : Fin 5) : RepresentativeSpinModel :=
  representativeSpinPlanEnd representativeSpinIdentityModel
      (generatedFeasibleAmbientTenthMonomialPlan k)

/-- Each plan is bound to the actual root-two normalization word. -/
theorem generatedFeasibleAmbientTenth_monomial_word (k : Fin 5) :
    generatedFeasibleAmbientTenthMonomialWord k =
      generatedAxisGlobalFifthShortNormalizationWords 2 (Fin.castLE (by decide) k) := by
  fin_cases k <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
