/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSegments

/-! Literal bounded portions of original monomial word2, with its complete Parker phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual signed model at the start of bounded block0. -/
def generatedFifthPermutationPlan2Input0 : RepresentativeSpinModel :=
  representativeSpinIdentityModel

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan2Input1 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
    ((0, true),
      representativeSpinRowsModel
        ![256, 1885, 1239, 1615, 480, 1648, 491, 1259, 882, 586, 747, 2094]
        ![544, 1218, 992, 1696, 864, 416, 704, 896, 1792, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![312, 882, 192, 600, 1487, 1220, 871, 252, 1885, 1629, 115, 2094]
        ![393, 1520, 372, 1040, 1488, 544, 640, 1664, 256, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![936, 818, 692, 292, 1468, 267, 143, 923, 274, 664, 987, 2078]
        ![185, 1632, 112, 1656, 0, 32, 0, 512, 1024, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1035, 2038, 12, 1061, 1639, 1207, 64, 788, 564, 912, 2000, 3087]
        ![260, 260, 1092, 984, 608, 704, 896, 0, 1536, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1423, 1789, 1342, 1310, 439, 720, 1220, 852, 1660, 1065, 607, 3085]
        ![175, 1198, 344, 2000, 1008, 640, 896, 256, 1536, 0, 0, 0])
  ]

/-- The actual signed model at the start of bounded block2. -/
def generatedFifthPermutationPlan2Input2 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1423, 1789, 1342, 1310, 439, 720, 1220, 852, 1660, 1065, 607, 3085]
        ![175, 1198, 344, 2000, 1008, 640, 896, 256, 1536, 0, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![597, 1660, 613, 581, 310, 458, 4, 1039, 1789, 882, 639, 3085]
        ![717, 710, 1468, 1736, 464, 928, 1088, 1152, 0, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1936, 12, 2038, 1156, 284, 214, 1057, 46, 270, 1259, 42, 2255]
        ![763, 208, 2040, 1736, 1136, 128, 1856, 1152, 256, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1896, 8, 271, 1508, 1702, 1648, 949, 923, 1363, 1753, 1978, 2110]
        ![1207, 1148, 1004, 1904, 432, 1120, 192, 256, 1536, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![643, 1065, 1056, 761, 1652, 4, 252, 871, 1885, 1629, 210, 2191]
        ![110, 764, 744, 1128, 592, 736, 704, 128, 1024, 1024, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![256, 1885, 1239, 526, 1280, 267, 624, 912, 1065, 1706, 1547, 2191]
        ![1761, 34, 1796, 576, 1952, 1728, 1088, 384, 1792, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1259, 1117, 271, 1639, 779, 1035, 1435, 480, 1744, 1753, 736, 2110]
        ![1891, 120, 1536, 720, 2000, 64, 1408, 1408, 512, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![9, 1744, 1888, 8, 390, 1021, 1679, 1935, 1117, 182, 1416, 2110]
        ![1166, 1534, 1404, 128, 560, 800, 384, 1664, 512, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1147, 1239, 1885, 2027, 1031, 2042, 1153, 782, 1207, 1965, 1409, 2971]
        ![427, 236, 104, 232, 1936, 1952, 64, 1024, 1024, 0, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block3. -/
def generatedFifthPermutationPlan2Input3 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1147, 1239, 1885, 2027, 1031, 2042, 1153, 782, 1207, 1965, 1409, 2971]
        ![427, 236, 104, 232, 1936, 1952, 64, 1024, 1024, 0, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![143, 600, 1423, 546, 1533, 519, 1653, 1403, 504, 1466, 506, 3087]
        ![1194, 46, 1368, 1504, 832, 736, 64, 1664, 512, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1090, 504, 738, 1359, 1629, 1370, 1509, 534, 600, 727, 1623, 3087]
        ![75, 28, 540, 616, 1984, 576, 1984, 256, 512, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![782, 1465, 1753, 1038, 1096, 274, 1510, 2032, 161, 64, 533, 2683]
        ![1311, 1820, 1912, 0, 192, 448, 448, 640, 768, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1516, 92, 356, 292, 1363, 1089, 781, 1277, 1061, 16, 283, 3328]
        ![878, 1534, 668, 976, 1824, 1024, 1280, 0, 1280, 1536, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1077, 1061, 1220, 1156, 298, 664, 1037, 349, 92, 1456, 347, 3328]
        ![1598, 94, 120, 1056, 1008, 0, 576, 384, 1024, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![727, 761, 1753, 1495, 113, 946, 6, 1360, 376, 64, 908, 2683]
        ![14, 700, 1436, 1976, 1088, 1472, 1856, 896, 768, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1090, 97, 738, 1359, 1021, 963, 1756, 1366, 1217, 782, 1998, 3087]
        ![559, 1468, 1632, 1448, 1440, 1984, 1664, 1920, 1280, 512, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1999, 1217, 1487, 610, 1885, 1598, 172, 635, 97, 1059, 99, 3087]
        ![1518, 1902, 292, 1600, 1344, 1440, 1920, 0, 256, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block4. -/
def generatedFifthPermutationPlan2Input4 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1999, 1217, 1487, 610, 1885, 1598, 172, 635, 97, 1059, 99, 3087]
        ![1518, 1902, 292, 1600, 1344, 1440, 1920, 0, 256, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block4 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![1147, 526, 1533, 523, 1854, 355, 536, 727, 1326, 1965, 1048, 2971]
        ![2031, 2028, 500, 1096, 1072, 416, 128, 896, 256, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![745, 1072, 32, 1073, 806, 1629, 1743, 207, 1789, 2038, 1777, 3079]
        ![206, 94, 152, 1216, 976, 1024, 1920, 1408, 1280, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![267, 1789, 271, 1310, 491, 1771, 1435, 480, 1072, 1753, 736, 3079]
        ![770, 1912, 996, 504, 256, 1376, 1408, 1920, 768, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1536, 1533, 526, 1239, 512, 1259, 1936, 1648, 393, 659, 1003, 2255]
        ![1648, 98, 1504, 1848, 416, 352, 960, 1280, 256, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![794, 393, 864, 1465, 1652, 1508, 901, 1822, 1533, 1021, 1330, 2255]
        ![815, 1884, 748, 1824, 256, 1696, 1408, 1920, 512, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1041, 1073, 271, 4, 838, 912, 556, 1179, 298, 1753, 291, 3079]
        ![838, 1692, 1256, 552, 624, 672, 1664, 128, 1792, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![624, 469, 182, 292, 613, 214, 1464, 1719, 2007, 267, 851, 2191]
        ![397, 1256, 900, 696, 864, 1248, 1664, 0, 512, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![972, 581, 284, 1660, 310, 691, 1508, 783, 1117, 402, 159, 3085]
        ![397, 1894, 24, 1416, 1840, 1088, 320, 512, 0, 512, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block5. -/
def generatedFifthPermutationPlan2Input5 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![972, 581, 284, 1660, 310, 691, 1508, 783, 1117, 402, 159, 3085]
        ![397, 1894, 24, 1416, 1840, 1088, 320, 512, 0, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block5 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, false),
      representativeSpinRowsModel
        ![1487, 1117, 263, 1639, 1838, 48, 356, 788, 581, 393, 2047, 3085]
        ![574, 942, 1020, 1960, 240, 704, 832, 640, 1280, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1771, 182, 469, 92, 1310, 1326, 64, 852, 564, 1648, 560, 3087]
        ![1281, 1252, 120, 560, 368, 992, 384, 640, 512, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![145, 466, 756, 1156, 453, 1259, 1999, 1179, 946, 1089, 1243, 2919]
        ![1657, 288, 116, 2040, 1728, 1696, 640, 1664, 1024, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![225, 402, 128, 1217, 1423, 356, 1822, 901, 1533, 1021, 1098, 2487]
        ![1112, 1872, 1648, 808, 1136, 288, 512, 256, 1536, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1536, 1533, 526, 1615, 480, 912, 779, 267, 402, 371, 11, 2487]
        ![1424, 898, 1540, 944, 592, 864, 448, 384, 512, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1648, 390, 756, 613, 491, 624, 256, 512, 1363, 1089, 1659, 2919]
        ![1296, 1522, 0, 1888, 224, 128, 896, 640, 0, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![274, 1363, 323, 466, 1342, 933, 1975, 439, 390, 2038, 1770, 2919]
        ![831, 76, 156, 1232, 960, 800, 192, 1152, 0, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![768, 526, 1533, 523, 710, 355, 504, 79, 214, 597, 2040, 3840]
        ![998, 6, 528, 944, 976, 384, 192, 768, 256, 0, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block6. -/
def generatedFifthPermutationPlan2Input6 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![768, 526, 1533, 523, 710, 355, 504, 79, 214, 597, 2040, 3840]
        ![998, 6, 528, 944, 976, 384, 192, 768, 256, 0, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block6 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![556, 1465, 972, 409, 1598, 1885, 1359, 1280, 122, 1696, 1272, 2191]
        ![831, 604, 1848, 912, 2032, 1632, 1984, 512, 1792, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1754, 122, 761, 172, 1021, 672, 1092, 1077, 1465, 1941, 1709, 2191]
        ![232, 0, 284, 736, 1648, 192, 1280, 640, 1792, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![79, 738, 1089, 980, 906, 298, 6, 1075, 376, 1464, 119, 3328]
        ![528, 450, 736, 1456, 720, 1632, 0, 256, 512, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1366, 1702, 1468, 4, 946, 664, 1037, 62, 292, 936, 56, 2683]
        ![785, 522, 1796, 1024, 336, 1440, 768, 896, 1280, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![2032, 1696, 1218, 1898, 1756, 1092, 349, 355, 501, 1771, 1390, 2971]
        ![1705, 1756, 1888, 800, 672, 1792, 1152, 384, 1280, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1822, 501, 889, 209, 393, 504, 1039, 1752, 1696, 336, 1734, 2971]
        ![785, 594, 740, 304, 416, 64, 960, 1280, 512, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![62, 491, 685, 1021, 81, 425, 783, 1495, 10, 1154, 472, 2397]
        ![814, 502, 1520, 2032, 1920, 32, 1472, 384, 768, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1160, 10, 2042, 1706, 432, 720, 1216, 128, 491, 469, 136, 2397]
        ![1039, 14, 1036, 1024, 1120, 704, 1024, 1280, 768, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block7. -/
def generatedFifthPermutationPlan2Input7 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1160, 10, 2042, 1706, 432, 720, 1216, 128, 491, 469, 136, 2397]
        ![1039, 14, 1036, 1024, 1120, 704, 1024, 1280, 768, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan2Block7 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![1752, 2, 1508, 1073, 1456, 1888, 64, 192, 1536, 1280, 1024, 3840]
        ![816, 1792, 740, 464, 688, 352, 768, 1664, 1536, 1024, 1024, 0])
  ]

/-- The bounded blocks are definitionally the entire original literal plan. -/
theorem generatedFifth_permutation_plan2_blocks :
    generatedFifthMonomialPermutationSpinPlan 2 =
      generatedFifthPermutationPlan2Block0 ++
      generatedFifthPermutationPlan2Block1 ++
      generatedFifthPermutationPlan2Block2 ++
      generatedFifthPermutationPlan2Block3 ++
      generatedFifthPermutationPlan2Block4 ++
      generatedFifthPermutationPlan2Block5 ++
      generatedFifthPermutationPlan2Block6 ++
      generatedFifthPermutationPlan2Block7 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
