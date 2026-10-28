/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSegments

/-! Literal bounded portions of original monomial word4, with its complete Parker phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual signed model at the start of bounded block0. -/
def generatedFifthPermutationPlan4Input0 : RepresentativeSpinModel :=
  representativeSpinIdentityModel

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan4Input1 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan4Input2 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1871, 738, 664, 980, 2035, 1363, 1510, 10, 161, 1057, 430, 3328]
        ![800, 386, 4, 352, 1376, 1120, 1216, 256, 0, 1536, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan4Input3 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1648, 1660, 692, 581, 624, 1771, 1536, 1280, 81, 664, 379, 3069]
        ![49, 242, 1792, 264, 1680, 64, 1600, 896, 512, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
    ((0, true),
      representativeSpinRowsModel
        ![267, 1702, 12, 779, 1653, 1089, 1754, 1510, 143, 46, 826, 2971]
        ![1238, 714, 560, 536, 560, 1888, 704, 1280, 0, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![172, 122, 727, 761, 1092, 5, 269, 1259, 466, 882, 561, 2078]
        ![1395, 862, 992, 360, 528, 1632, 192, 1024, 0, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![672, 466, 371, 349, 1516, 9, 781, 1871, 122, 214, 543, 2078]
        ![1784, 244, 1708, 1672, 512, 1888, 640, 1920, 768, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![775, 1160, 12, 263, 2035, 1509, 1360, 1090, 643, 46, 280, 2971]
        ![1885, 878, 1368, 2000, 544, 1088, 128, 1664, 768, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![685, 643, 1965, 1702, 504, 92, 323, 995, 1160, 1935, 19, 2971]
        ![355, 2034, 332, 760, 288, 1856, 128, 1152, 768, 512, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block4. -/
def generatedFifthPermutationPlan4Input4 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![685, 643, 1965, 1702, 504, 92, 323, 995, 1160, 1935, 19, 2971]
        ![355, 2034, 332, 760, 288, 1856, 128, 1152, 768, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block4 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![274, 371, 466, 1629, 838, 794, 30, 1021, 1224, 1660, 702, 3085]
        ![1347, 1076, 424, 1752, 1056, 384, 768, 640, 1536, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![692, 1224, 1999, 64, 1789, 1207, 1045, 1504, 371, 97, 1329, 3085]
        ![1402, 1766, 1788, 712, 1696, 608, 192, 0, 1792, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![267, 263, 1965, 1280, 972, 586, 209, 501, 1838, 1935, 1082, 2971]
        ![765, 266, 564, 1344, 928, 768, 832, 640, 1792, 0, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![425, 1456, 1465, 1466, 2038, 390, 1487, 292, 1453, 685, 1427, 2110]
        ![1256, 1024, 0, 232, 16, 0, 832, 640, 0, 0, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1792, 1453, 781, 782, 2027, 1147, 1691, 1936, 1456, 1049, 1424, 2110]
        ![446, 1468, 668, 1048, 1056, 2016, 704, 896, 512, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1435, 1197, 1533, 1743, 635, 912, 512, 267, 10, 3, 11, 3087]
        ![892, 708, 1432, 736, 96, 352, 0, 128, 0, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1915, 214, 172, 581, 624, 491, 256, 779, 2032, 818, 1904, 2127]
        ![1330, 1850, 4, 1184, 736, 384, 704, 256, 512, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1218, 2032, 1075, 1754, 1366, 349, 527, 1940, 214, 1965, 1433, 2127]
        ![248, 642, 400, 896, 304, 1184, 576, 640, 512, 512, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block5. -/
def generatedFifthPermutationPlan4Input5 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1218, 2032, 1075, 1754, 1366, 349, 527, 1940, 214, 1965, 1433, 2127]
        ![248, 642, 400, 896, 304, 1184, 576, 640, 512, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block5 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![523, 1533, 1197, 768, 1037, 1360, 1216, 852, 597, 1653, 347, 3840]
        ![1006, 12, 1468, 1208, 2016, 352, 1920, 256, 768, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1039, 2034, 1652, 1, 1885, 525, 1220, 1936, 409, 48, 848, 2775]
        ![1153, 160, 164, 1280, 1856, 1888, 128, 0, 1792, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![425, 409, 1465, 972, 310, 1696, 1487, 1117, 2034, 1021, 1317, 2775]
        ![958, 604, 1976, 1968, 1904, 832, 1856, 128, 512, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![852, 225, 818, 207, 1466, 794, 1310, 323, 8, 1152, 1164, 3083]
        ![1424, 416, 116, 2024, 1424, 1696, 1728, 1024, 768, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![269, 1326, 271, 1423, 610, 376, 901, 710, 1516, 1096, 2008, 2683]
        ![1639, 174, 1176, 1040, 160, 160, 576, 256, 256, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![691, 48, 1049, 81, 1207, 1487, 1942, 1360, 469, 1771, 1749, 2048]
        ![1478, 986, 956, 624, 1056, 1312, 1856, 128, 1792, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1854, 469, 113, 1081, 1362, 1216, 788, 312, 48, 643, 669, 2048]
        ![1793, 416, 112, 608, 1264, 1312, 192, 0, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![710, 624, 949, 310, 241, 1073, 1935, 1719, 889, 713, 1443, 3085]
        ![871, 1630, 604, 1056, 832, 864, 1600, 1024, 1536, 0, 0, 0])
  ]

/-- The actual signed model at the start of bounded block6. -/
def generatedFifthPermutationPlan4Input6 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![710, 624, 949, 310, 241, 1073, 1935, 1719, 889, 713, 1443, 3085]
        ![871, 1630, 604, 1056, 832, 864, 1600, 1024, 1536, 0, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan4Block6 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![432, 889, 458, 841, 504, 1088, 1160, 1224, 624, 182, 1824, 3085]
        ![1823, 796, 1688, 360, 1600, 1632, 256, 1152, 1280, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![312, 145, 356, 466, 1896, 808, 1744, 536, 1435, 1936, 1680, 3840]
        ![1816, 1226, 112, 296, 1584, 1696, 320, 1408, 256, 1536, 0, 0])
  ]

/-- The bounded blocks are definitionally the entire original literal plan. -/
theorem generatedFifth_permutation_plan4_blocks :
    generatedFifthMonomialPermutationSpinPlan 4 =
      generatedFifthPermutationPlan4Block0 ++
      generatedFifthPermutationPlan4Block1 ++
      generatedFifthPermutationPlan4Block2 ++
      generatedFifthPermutationPlan4Block3 ++
      generatedFifthPermutationPlan4Block4 ++
      generatedFifthPermutationPlan4Block5 ++
      generatedFifthPermutationPlan4Block6 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
