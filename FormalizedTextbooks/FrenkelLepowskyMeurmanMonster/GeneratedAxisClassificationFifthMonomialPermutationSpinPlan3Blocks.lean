/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSegments

/-! Literal bounded portions of original monomial word3, with its complete Parker phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual signed model at the start of bounded block0. -/
def generatedFifthPermutationPlan3Input0 : RepresentativeSpinModel :=
  representativeSpinIdentityModel

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![241, 1075, 355, 659, 1040, 48, 1152, 192, 779, 12, 1265, 3069]
        ![1038, 14, 1032, 1032, 880, 928, 960, 896, 1536, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![775, 779, 1453, 1629, 808, 841, 1039, 1038, 1075, 1218, 1793, 3069]
        ![184, 110, 1132, 1120, 656, 1376, 1600, 384, 0, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![871, 1900, 889, 1000, 1065, 97, 783, 1, 1696, 1008, 1126, 2971]
        ![2016, 2034, 0, 1896, 896, 32, 0, 896, 1792, 1024, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1360, 1696, 1154, 1043, 1509, 420, 1277, 2042, 1900, 1035, 1271, 2971]
        ![394, 740, 708, 840, 48, 1248, 64, 768, 0, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![534, 838, 453, 1508, 274, 1089, 781, 775, 1156, 145, 1761, 2683]
        ![1842, 1586, 1504, 1896, 128, 32, 704, 896, 1024, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1871, 738, 664, 980, 2035, 1363, 1510, 10, 161, 1057, 430, 3328]
        ![800, 386, 4, 352, 1376, 1120, 1216, 256, 0, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![3, 1699, 1465, 1653, 1629, 672, 420, 1516, 761, 332, 429, 2255]
        ![748, 1792, 1376, 512, 880, 768, 576, 384, 768, 1024, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block1. -/
def generatedFifthPermutationPlan3Input1 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![768, 1239, 1885, 2027, 102, 2042, 97, 1871, 214, 972, 353, 2048]
        ![544, 1086, 1164, 208, 240, 64, 192, 128, 1280, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![946, 298, 154, 818, 263, 1948, 1582, 1838, 806, 182, 723, 2078]
        ![318, 76, 1400, 472, 1072, 1440, 64, 1280, 0, 1536, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![912, 806, 692, 284, 779, 1936, 1536, 1280, 298, 664, 379, 2078]
        ![784, 1874, 740, 1632, 1024, 256, 64, 1920, 512, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![946, 298, 154, 818, 263, 1948, 1582, 1838, 806, 182, 723, 2078]
        ![318, 76, 1400, 472, 1072, 1440, 64, 1280, 0, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![768, 1239, 1885, 2027, 102, 2042, 97, 1871, 214, 972, 353, 2048]
        ![544, 1086, 1164, 208, 240, 64, 192, 128, 1280, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![3, 1699, 1465, 1653, 1629, 672, 420, 1516, 761, 332, 429, 2255]
        ![748, 1792, 1376, 512, 880, 768, 576, 384, 768, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1871, 738, 664, 980, 2035, 1363, 1510, 10, 161, 1057, 430, 3328]
        ![800, 386, 4, 352, 1376, 1120, 1216, 256, 0, 1536, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block2. -/
def generatedFifthPermutationPlan3Input2 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1871, 738, 664, 980, 2035, 1363, 1510, 10, 161, 1057, 430, 3328]
        ![800, 386, 4, 352, 1376, 1120, 1216, 256, 0, 1536, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![534, 838, 453, 1508, 274, 1089, 781, 775, 1156, 145, 1761, 2683]
        ![1842, 1586, 1504, 1896, 128, 32, 704, 896, 1024, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1045, 1156, 4, 1061, 1744, 1753, 1942, 710, 838, 336, 704, 2683]
        ![591, 1068, 1180, 1208, 1072, 160, 576, 512, 1024, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![332, 600, 664, 1495, 1040, 9, 6, 1360, 1698, 1057, 908, 3328]
        ![1150, 1982, 376, 688, 464, 704, 1088, 128, 0, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![3, 1153, 1465, 1653, 1948, 1049, 1756, 1366, 1088, 1871, 911, 2255]
        ![477, 156, 676, 40, 128, 96, 1088, 1280, 768, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![783, 1088, 1652, 1464, 1885, 1566, 2007, 1691, 1153, 1154, 67, 2255]
        ![788, 602, 536, 848, 848, 896, 1536, 1024, 768, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![768, 1615, 519, 523, 1822, 323, 1752, 332, 756, 972, 835, 2048]
        ![272, 82, 1704, 1064, 144, 64, 1152, 1408, 1024, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![713, 81, 32, 209, 1117, 1629, 527, 1940, 1660, 12, 394, 3069]
        ![1870, 174, 156, 1072, 0, 256, 576, 896, 1024, 512, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1648, 1660, 692, 581, 624, 1771, 1536, 1280, 81, 664, 379, 3069]
        ![49, 242, 1792, 264, 1680, 64, 1600, 896, 512, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block3. -/
def generatedFifthPermutationPlan3Input3 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1648, 1660, 692, 581, 624, 1771, 1536, 1280, 81, 664, 379, 3069]
        ![49, 242, 1792, 264, 1680, 64, 1600, 896, 512, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![1435, 519, 1615, 1239, 1403, 912, 1035, 267, 691, 425, 1803, 3087]
        ![598, 1222, 668, 2040, 352, 1984, 0, 1664, 0, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1792, 1031, 30, 439, 2027, 1147, 1936, 1691, 1699, 1696, 656, 2110]
        ![687, 1052, 1432, 1696, 1424, 1248, 704, 128, 1280, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![3, 1699, 1465, 1040, 1359, 564, 1756, 828, 1031, 775, 825, 2110]
        ![1475, 448, 1796, 1712, 384, 1376, 704, 1024, 768, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![664, 738, 1615, 980, 1654, 1915, 5, 1504, 1456, 425, 417, 3087]
        ![913, 176, 0, 224, 1392, 352, 0, 1408, 256, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1648, 214, 692, 581, 2007, 269, 1089, 1509, 1975, 1435, 2001, 3069]
        ![637, 342, 372, 840, 1056, 1728, 1280, 1792, 1280, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![270, 1965, 1117, 271, 6, 1754, 564, 420, 1743, 241, 1759, 2094]
        ![1854, 664, 552, 1096, 1920, 96, 768, 1024, 768, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1598, 1743, 527, 1885, 356, 600, 390, 2038, 1965, 1699, 909, 2094]
        ![1855, 1432, 1228, 672, 1056, 1344, 384, 0, 1024, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![912, 692, 214, 1653, 1239, 1679, 963, 1077, 1639, 1691, 1459, 2127]
        ![1612, 2042, 448, 1216, 1440, 736, 1088, 128, 0, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block4. -/
def generatedFifthPermutationPlan3Input4 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![912, 692, 214, 1653, 1239, 1679, 963, 1077, 1639, 1691, 1459, 2127]
        ![1612, 2042, 448, 1216, 1440, 736, 1088, 128, 0, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block4 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![298, 818, 1789, 102, 756, 1147, 469, 1504, 1888, 889, 1571, 2397]
        ![576, 418, 1508, 1000, 1024, 1216, 1664, 1792, 512, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![177, 241, 857, 32, 1533, 390, 828, 1756, 1031, 775, 1801, 3086]
        ![1042, 642, 736, 1128, 16, 1536, 512, 1152, 1536, 0, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1792, 1031, 30, 871, 267, 1915, 624, 1435, 241, 64, 1136, 3086]
        ![1102, 1886, 892, 72, 1744, 1888, 1792, 1280, 1280, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1691, 263, 1789, 2007, 1403, 1648, 491, 2027, 209, 889, 747, 2397]
        ![1749, 1150, 1144, 112, 1552, 320, 1088, 1280, 1024, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![912, 1660, 214, 1653, 1936, 779, 1280, 1536, 995, 298, 379, 2127]
        ![1024, 1954, 740, 512, 848, 192, 640, 896, 1792, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![713, 995, 1040, 691, 527, 783, 1117, 710, 1660, 1516, 2008, 2127]
        ![431, 1452, 1400, 1080, 224, 864, 960, 512, 1024, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![768, 1789, 263, 1259, 1822, 1041, 906, 332, 1654, 284, 1297, 2048]
        ![529, 1102, 252, 160, 304, 384, 384, 1024, 1024, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1629, 672, 806, 570, 271, 1310, 1239, 1435, 1075, 1154, 1553, 2733]
        ![935, 1504, 1276, 232, 1024, 32, 64, 256, 256, 1536, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block5. -/
def generatedFifthPermutationPlan3Input5 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1629, 672, 806, 570, 271, 1310, 1239, 1435, 1075, 1154, 1553, 2733]
        ![935, 1504, 1276, 232, 1024, 32, 64, 256, 256, 1536, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block5 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![177, 1075, 857, 581, 1948, 1049, 828, 1508, 672, 1277, 1805, 2733]
        ![12, 418, 272, 1184, 208, 896, 960, 1664, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![332, 1754, 298, 1495, 32, 1081, 356, 1152, 402, 371, 1980, 3584]
        ![671, 14, 1180, 104, 1424, 320, 256, 1280, 0, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![501, 1510, 182, 453, 1744, 745, 788, 1940, 1220, 128, 1776, 2683]
        ![1966, 942, 376, 1376, 1296, 352, 832, 896, 0, 512, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1092, 1220, 1061, 1366, 2034, 963, 1935, 775, 1510, 1043, 1923, 2683]
        ![723, 1970, 4, 1456, 256, 1184, 1984, 1920, 0, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1277, 818, 298, 102, 113, 1073, 1156, 1160, 1059, 371, 894, 3584]
        ![801, 416, 1504, 184, 1360, 96, 64, 128, 1280, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![177, 241, 857, 581, 783, 1088, 2038, 12, 761, 332, 975, 2733]
        ![829, 236, 52, 104, 1600, 1088, 640, 1280, 1792, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![949, 761, 597, 841, 263, 1359, 1533, 256, 241, 64, 723, 2733]
        ![927, 92, 1496, 464, 1344, 1344, 448, 1024, 0, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![768, 2007, 271, 267, 980, 1096, 979, 1277, 692, 284, 467, 2048]
        ![289, 754, 1080, 696, 1680, 1088, 192, 1792, 0, 1024, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block6. -/
def generatedFifthPermutationPlan3Input6 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![768, 2007, 271, 267, 980, 1096, 979, 1277, 692, 284, 467, 2048]
        ![289, 754, 1080, 696, 1680, 1088, 192, 1792, 0, 1024, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block6 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![946, 664, 504, 738, 519, 1948, 1326, 1838, 1652, 4, 609, 2078]
        ![575, 1502, 156, 464, 512, 0, 768, 0, 1792, 512, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1648, 1652, 214, 972, 1771, 624, 1280, 1536, 664, 298, 379, 2078]
        ![785, 672, 1792, 1976, 480, 1664, 832, 128, 1024, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![946, 664, 504, 738, 519, 1948, 1326, 1838, 1652, 4, 609, 2078]
        ![575, 1502, 156, 464, 512, 0, 768, 0, 1792, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![768, 2007, 271, 267, 980, 1096, 979, 1277, 692, 284, 467, 2048]
        ![289, 754, 1080, 696, 1680, 1088, 192, 1792, 0, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![949, 761, 597, 841, 263, 1359, 1533, 256, 241, 64, 723, 2733]
        ![927, 92, 1496, 464, 1344, 1344, 448, 1024, 0, 1536, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![177, 241, 857, 581, 783, 1088, 2038, 12, 761, 332, 975, 2733]
        ![829, 236, 52, 104, 1600, 1088, 640, 1280, 1792, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1277, 818, 298, 102, 113, 1073, 1156, 1160, 1059, 371, 894, 3584]
        ![801, 416, 1504, 184, 1360, 96, 64, 128, 1280, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1092, 1220, 1061, 1366, 2034, 963, 1935, 775, 1510, 1043, 1923, 2683]
        ![723, 1970, 4, 1456, 256, 1184, 1984, 1920, 0, 512, 0, 0])
  ]

/-- The actual signed model at the start of bounded block7. -/
def generatedFifthPermutationPlan3Input7 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1092, 1220, 1061, 1366, 2034, 963, 1935, 775, 1510, 1043, 1923, 2683]
        ![723, 1970, 4, 1456, 256, 1184, 1984, 1920, 0, 512, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan3Block7 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![1152, 64, 1154, 145, 1077, 2038, 1871, 1096, 92, 491, 967, 2971]
        ![1001, 606, 704, 1216, 160, 1792, 1664, 1920, 768, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![439, 92, 425, 1466, 1065, 979, 1629, 355, 64, 1216, 2004, 2971]
        ![209, 1216, 1508, 1456, 1648, 352, 1920, 1536, 0, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![775, 1771, 1999, 783, 586, 409, 349, 62, 1153, 546, 1635, 2127]
        ![11, 696, 2008, 1720, 0, 480, 768, 768, 0, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1699, 1153, 1, 1217, 32, 48, 1360, 2032, 1771, 1516, 675, 2127]
        ![1039, 1036, 1036, 1024, 1984, 1472, 192, 128, 0, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![355, 466, 182, 1370, 1056, 1040, 1696, 336, 512, 256, 1024, 2048]
        ![1073, 1360, 1508, 8, 352, 960, 448, 768, 256, 1024, 0, 0])
  ]

/-- The bounded blocks are definitionally the entire original literal plan. -/
theorem generatedFifth_permutation_plan3_blocks :
    generatedFifthMonomialPermutationSpinPlan 3 =
      generatedFifthPermutationPlan3Block0 ++
      generatedFifthPermutationPlan3Block1 ++
      generatedFifthPermutationPlan3Block2 ++
      generatedFifthPermutationPlan3Block3 ++
      generatedFifthPermutationPlan3Block4 ++
      generatedFifthPermutationPlan3Block5 ++
      generatedFifthPermutationPlan3Block6 ++
      generatedFifthPermutationPlan3Block7 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
