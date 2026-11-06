/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthXiTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsFastDecision

/-! Bounded signed spin plans for the original sixth transporter, Xi transporter, and swap words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The three actual original full-fiber permutation words used in the corrected lifts. -/
def generatedSixthPermutationProfileWords : Fin 3 → List (Fin 4) :=
  ![leechRootedA2SixthPermutationTransportWord, leechRootedA2SixthXiTransportWord,
    leechRootedA2SixthPermutationSwapWord]

/-- Every intermediate signed pullback model, retaining its original source letter. -/
def generatedSixthPermutationSpinPlans : Fin 3 → RepresentativeSpinPlan (Fin 4) :=
  ![[
      (1,
        representativeSpinRowsModel
          ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
          ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
          ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0]),
      (1,
        representativeSpinRowsModel
          ![972, 1464, 1465, 1466, 1065, 1370, 1702, 1045, 1935, 1871, 1807, 2255]
          ![1084, 2046, 0, 8, 528, 288, 512, 384, 512, 0, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![12, 8, 519, 263, 806, 371, 794, 691, 782, 3, 1795, 2048]
          ![818, 240, 700, 368, 528, 288, 768, 896, 256, 512, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![1008, 1362, 355, 402, 1061, 597, 1456, 425, 526, 768, 1267, 3069]
          ![1086, 254, 44, 16, 864, 896, 448, 512, 0, 512, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![409, 1057, 841, 46, 214, 1648, 1370, 1049, 1598, 241, 1386, 2971]
          ![368, 1178, 2008, 864, 16, 1920, 1664, 128, 1280, 1536, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![1743, 1598, 1536, 1383, 713, 1756, 672, 336, 1057, 1464, 1549, 2971]
          ![1377, 2, 1936, 1584, 1264, 416, 1344, 512, 1792, 0, 1024, 0]),
      (2,
        representativeSpinRowsModel
          ![323, 355, 1362, 234, 523, 1239, 818, 610, 453, 1326, 194, 3079]
          ![110, 962, 2040, 1544, 1264, 480, 1408, 384, 1792, 1536, 1024, 0]),
      (2,
        representativeSpinRowsModel
          ![2038, 963, 979, 1789, 906, 1885, 209, 691, 1771, 1510, 385, 2919]
          ![30, 1584, 1304, 1032, 544, 1888, 1600, 256, 1792, 1536, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![781, 1771, 512, 1838, 1698, 527, 376, 864, 963, 1077, 1199, 2919]
          ![1377, 2008, 1660, 752, 1072, 480, 0, 384, 512, 1024, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![1464, 1508, 1362, 1041, 525, 1197, 1999, 536, 1342, 1326, 279, 3079]
          ![62, 1020, 96, 296, 2000, 1664, 1664, 1152, 1792, 1024, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![1743, 2027, 1536, 1383, 794, 1696, 783, 1495, 1117, 323, 2008, 2971]
          ![959, 602, 788, 1152, 1008, 1984, 1856, 1408, 1792, 1536, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![1453, 838, 214, 1706, 1218, 1466, 527, 1752, 349, 871, 629, 2127]
          ![962, 1900, 1568, 1112, 1696, 320, 1024, 128, 0, 0, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![570, 349, 1370, 806, 1753, 1465, 1435, 852, 838, 1771, 1033, 2127]
          ![883, 952, 1284, 1048, 1408, 1696, 1472, 896, 1024, 1024, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![1941, 1038, 3, 1, 720, 864, 1885, 1743, 1516, 1660, 924, 3083]
          ![433, 864, 432, 432, 1696, 1376, 0, 1152, 1280, 512, 1024, 0])],
    [
      (2,
        representativeSpinRowsModel
          ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
          ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
      (1,
        representativeSpinRowsModel
          ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
          ![527, 14, 12, 0, 16, 0, 64, 128, 256, 1024, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
          ![556, 2, 208, 120, 16, 512, 64, 640, 768, 512, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![241, 1598, 355, 659, 1096, 564, 1756, 713, 271, 1, 1788, 3069]
          ![71, 12, 576, 536, 352, 928, 384, 768, 1792, 1024, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![270, 271, 1965, 1117, 889, 284, 1035, 1031, 1598, 1743, 1292, 3069]
          ![621, 616, 552, 1088, 560, 1312, 1728, 256, 768, 1536, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![871, 1896, 808, 432, 1653, 613, 267, 12, 1197, 1008, 1643, 2971]
          ![1462, 1532, 1092, 1448, 848, 32, 128, 256, 1536, 512, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![1648, 1652, 972, 390, 30, 1040, 1639, 263, 738, 664, 27, 2094]
          ![1072, 480, 1652, 1200, 480, 1024, 1728, 1792, 0, 1536, 0, 0]),
      (1,
        representativeSpinRowsModel
          ![122, 738, 336, 794, 1160, 1153, 252, 923, 1652, 4, 593, 2094]
          ![1098, 938, 2040, 1952, 1680, 1152, 1984, 1536, 1792, 1024, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![788, 192, 145, 1423, 1753, 9, 458, 871, 2034, 586, 325, 3840]
          ![869, 246, 232, 1448, 32, 1024, 128, 1152, 1536, 512, 0, 0]),
      (1,
        representativeSpinRowsModel
          ![1464, 2034, 271, 1041, 491, 1516, 643, 761, 192, 980, 1115, 3840]
          ![1264, 628, 744, 1488, 480, 864, 384, 896, 1536, 1024, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![685, 336, 738, 310, 8, 1508, 409, 864, 1679, 1156, 483, 2919]
          ![2036, 162, 536, 984, 256, 1952, 1920, 640, 768, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1065, 979, 161, 1061, 838, 1698, 439, 727, 525, 1885, 846, 2078]
          ![1040, 1520, 608, 1896, 224, 1824, 1280, 0, 1536, 1024, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![92, 586, 1975, 234, 1057, 643, 1031, 1744, 1075, 1218, 1895, 2971]
          ![2014, 684, 120, 208, 1712, 1536, 1024, 1152, 1280, 1024, 1024, 0])],
    [
      (1,
        representativeSpinRowsModel
          ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
          ![829, 254, 8, 0, 512, 256, 512, 256, 0, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
          ![1854, 1278, 688, 368, 512, 256, 768, 768, 512, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![691, 1453, 1698, 214, 466, 1679, 1359, 97, 92, 556, 1996, 3083]
          ![1629, 1836, 1220, 368, 1600, 1408, 1984, 256, 512, 1536, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![624, 92, 912, 1508, 1059, 525, 270, 1363, 1453, 1822, 440, 3083]
          ![1073, 2032, 968, 1984, 1472, 1760, 1280, 640, 1280, 0, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![3, 1466, 1154, 1090, 1435, 1582, 1259, 1117, 1403, 1652, 443, 2255]
          ![807, 596, 1400, 1984, 336, 640, 1792, 1536, 1280, 1536, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![783, 1403, 1871, 1935, 1370, 1065, 1504, 1936, 1466, 1465, 379, 2255]
          ![495, 924, 1036, 1656, 656, 320, 1600, 1024, 1792, 1024, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![12, 1660, 519, 263, 1057, 371, 1771, 624, 504, 192, 375, 2048]
          ![231, 404, 12, 368, 656, 320, 1472, 1920, 0, 512, 0, 0]),
      (1,
        representativeSpinRowsModel
          ![312, 504, 1207, 1975, 933, 355, 1999, 1216, 1660, 1648, 631, 2048]
          ![1122, 930, 1704, 352, 832, 160, 64, 128, 256, 1536, 1024, 0]),
      (2,
        representativeSpinRowsModel
          ![1179, 1871, 1403, 779, 234, 393, 64, 1152, 1706, 9, 847, 2539]
          ![1102, 142, 12, 200, 688, 672, 192, 1664, 768, 0, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![1699, 1706, 1702, 214, 271, 1342, 1743, 1885, 1871, 980, 1343, 2539]
          ![275, 1746, 984, 2008, 976, 32, 1856, 384, 512, 1024, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1216, 1224, 128, 852, 659, 1965, 526, 1363, 781, 1822, 924, 2191]
          ![1057, 2034, 2012, 2008, 288, 960, 1600, 768, 1024, 0, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![1043, 781, 1942, 1090, 1366, 267, 1147, 581, 1224, 8, 72, 2191]
          ![457, 168, 1504, 1240, 1312, 192, 512, 1792, 768, 1024, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![1648, 779, 1702, 5, 1310, 1117, 525, 1598, 1948, 980, 1592, 2539]
          ![1838, 606, 304, 1240, 1216, 800, 64, 1536, 1024, 512, 1024, 0]),
      (1,
        representativeSpinRowsModel
          ![1096, 1948, 9, 1706, 393, 234, 1154, 145, 779, 1403, 155, 2539]
          ![1304, 1738, 736, 784, 720, 352, 64, 1664, 1024, 1024, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1075, 1942, 781, 1654, 1370, 1456, 192, 81, 1756, 4, 1235, 3584]
          ![1566, 510, 8, 1296, 304, 192, 1152, 1152, 1280, 1536, 1024, 0]),
      (3,
        representativeSpinRowsModel
          ![1752, 1756, 172, 1495, 1040, 1465, 546, 1008, 1942, 933, 424, 3584]
          ![463, 1214, 12, 688, 400, 1600, 192, 512, 512, 1024, 1024, 0]),
      (2,
        representativeSpinRowsModel
          ![145, 1156, 788, 177, 864, 1753, 1698, 1362, 1218, 2032, 1904, 2127]
          ![1262, 1084, 236, 1976, 448, 1408, 1728, 512, 1024, 0, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![794, 1702, 1696, 336, 1153, 600, 1041, 323, 225, 207, 2017, 3840]
          ![1512, 1164, 136, 104, 896, 512, 1344, 1920, 1280, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1, 4, 1216, 1039, 122, 546, 425, 234, 1326, 453, 1275, 2110]
          ![887, 714, 1168, 1568, 208, 32, 832, 512, 1280, 1024, 1024, 0]),
      (3,
        representativeSpinRowsModel
          ![1259, 1326, 1280, 1487, 1360, 1154, 995, 298, 4, 5, 1076, 2110]
          ![476, 1286, 156, 1288, 272, 736, 512, 896, 1536, 0, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![2032, 1059, 1696, 1466, 356, 466, 1310, 713, 1035, 207, 964, 3840]
          ![936, 1894, 104, 1896, 576, 32, 64, 640, 1536, 1536, 0, 0]),
      (0,
        representativeSpinRowsModel
          ![145, 161, 788, 177, 672, 182, 269, 2007, 685, 794, 853, 2127]
          ![911, 510, 1928, 624, 0, 768, 832, 512, 1280, 1536, 0, 0]),
      (3,
        representativeSpinRowsModel
          ![439, 685, 62, 923, 172, 912, 781, 1277, 161, 48, 240, 2127]
          ![385, 594, 976, 1288, 16, 256, 320, 512, 1536, 512, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1754, 1696, 1059, 1043, 491, 635, 1719, 586, 1160, 64, 327, 3328]
          ![918, 1940, 1692, 984, 720, 736, 320, 640, 1280, 0, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![1771, 1453, 1935, 1999, 1654, 1037, 864, 298, 8, 9, 1949, 2971]
          ![350, 1444, 1772, 464, 768, 320, 0, 0, 1280, 1024, 0, 0]),
      (2,
        representativeSpinRowsModel
          ![972, 794, 1456, 1465, 1792, 781, 828, 534, 1896, 527, 374, 2078]
          ![1543, 1708, 1092, 256, 832, 480, 640, 512, 256, 512, 0, 0]),
      (3,
        representativeSpinRowsModel
          ![1383, 1896, 1897, 1888, 882, 1154, 536, 207, 794, 214, 383, 2078]
          ![815, 2, 8, 936, 784, 512, 320, 896, 768, 512, 1024, 0]),
      (0,
        representativeSpinRowsModel
          ![64, 1152, 1935, 356, 525, 2032, 432, 727, 1699, 9, 319, 2971]
          ![725, 768, 672, 1488, 848, 640, 960, 256, 1792, 1536, 0, 0]),
      (3,
        representativeSpinRowsModel
          ![1706, 1699, 838, 1453, 46, 979, 889, 1566, 1152, 1216, 2004, 2971]
          ![1793, 482, 676, 1864, 1936, 608, 1344, 1280, 1536, 512, 1024, 0])]]

/-- Exact coordinate rows of the three bounded original spin word profiles. -/
def generatedSixthPermutationProfileCoordinateRows : Fin 3 → Fin 12 → Fin 4096 :=
  ![![1941, 1038, 3, 1, 720, 864, 1885, 1743, 1516, 1660, 924, 3083],
    ![92, 586, 1975, 234, 1057, 643, 1031, 1744, 1075, 1218, 1895, 2971],
    ![1706, 1699, 838, 1453, 46, 979, 889, 1566, 1152, 1216, 2004, 2971]]

/-- Exact phase rows of the three bounded original spin word profiles. -/
def generatedSixthPermutationProfilePhaseRows : Fin 3 → Fin 12 → Fin 4096 :=
  ![![433, 864, 432, 432, 1696, 1376, 0, 1152, 1280, 512, 1024, 0],
    ![2014, 684, 120, 208, 1712, 1536, 1024, 1152, 1280, 1024, 1024, 0],
    ![1793, 482, 676, 1864, 1936, 608, 1344, 1280, 1536, 512, 1024, 0]]

/-- Exact inversecoordinate rows of the three bounded original spin word profiles. -/
def generatedSixthPermutationProfileInverseCoordinateRows : Fin 3 → Fin 12 → Fin 4096 :=
  ![![8, 12, 1031, 775, 154, 252, 420, 738, 692, 972, 1806, 3085],
    ![761, 1838, 643, 225, 1598, 1533, 1117, 1639, 1648, 912, 1812, 2191],
    ![781, 1629, 1771, 782, 857, 936, 768, 1691, 1096, 2042, 1947, 2094]]

/-- Exact inversephase rows of the three bounded original spin word profiles. -/
def generatedSixthPermutationProfileInversePhaseRows : Fin 3 → Fin 12 → Fin 4096 :=
  ![![0, 378, 768, 736, 672, 800, 960, 640, 0, 0, 1024, 0],
    ![1728, 416, 1396, 1072, 1696, 288, 384, 1024, 0, 512, 1024, 0],
    ![1181, 1286, 380, 1368, 48, 1216, 192, 1664, 256, 512, 0, 0]]

/-- The final signed model for each actual original full permutation word. -/
def generatedSixthPermutationProfileModel (k : Fin 3) : RepresentativeSpinModel :=
  representativeSpinRowsModel (generatedSixthPermutationProfileCoordinateRows k)
    (generatedSixthPermutationProfilePhaseRows k)

/-- Every planned letter is exactly the corresponding original source word letter. -/
theorem generatedSixth_permutation_profile_letters (k : Fin 3) :
    (generatedSixthPermutationSpinPlans k).map Prod.fst =
      generatedSixthPermutationProfileWords k := by
  fin_cases k <;> rfl

/-- The last explicit signed plan model is exactly the recorded original word profile. -/
theorem generatedSixth_permutation_profile_end (k : Fin 3) :
    representativeSpinPlanEnd representativeSpinIdentityModel
      (generatedSixthPermutationSpinPlans k) = generatedSixthPermutationProfileModel k := by
  fin_cases k <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
