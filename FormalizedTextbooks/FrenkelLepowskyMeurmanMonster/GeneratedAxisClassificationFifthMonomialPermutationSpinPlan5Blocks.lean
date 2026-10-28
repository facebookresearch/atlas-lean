/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSegments

/-! Literal bounded portions of original monomial word5, with its complete Parker phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual signed model at the start of bounded block0. -/
def generatedFifthPermutationPlan5Input0 : RepresentativeSpinModel :=
  representativeSpinIdentityModel

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan5Input1 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan5Input2 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1871, 738, 664, 980, 2035, 1363, 1510, 10, 161, 1057, 430, 3328]
        ![800, 386, 4, 352, 1376, 1120, 1216, 256, 0, 1536, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan5Input3 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1648, 1660, 692, 581, 624, 1771, 1536, 1280, 81, 664, 379, 3069]
        ![49, 242, 1792, 264, 1680, 64, 1600, 896, 512, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![1435, 519, 1615, 1239, 1403, 912, 1035, 267, 691, 425, 1803, 3087]
        ![598, 1222, 668, 2040, 352, 1984, 0, 1664, 0, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![794, 691, 122, 738, 1487, 292, 62, 1854, 519, 1948, 1427, 3087]
        ![16, 616, 368, 528, 976, 544, 1216, 1536, 0, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1280, 30, 1031, 923, 838, 610, 393, 1719, 1679, 525, 1673, 3083]
        ![778, 1158, 1892, 1264, 432, 1024, 640, 768, 256, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![469, 32, 1598, 1075, 207, 685, 1207, 512, 1000, 161, 905, 2127]
        ![1947, 604, 1500, 264, 896, 1664, 384, 1152, 1792, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![841, 1000, 1898, 1383, 775, 1706, 556, 852, 32, 501, 388, 2127]
        ![1299, 390, 240, 1776, 560, 1056, 640, 0, 1024, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1948, 1160, 1031, 263, 643, 1453, 720, 376, 1043, 525, 1560, 3083]
        ![799, 1884, 732, 912, 528, 1696, 384, 1280, 512, 0, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1566, 1043, 1310, 30, 536, 1495, 808, 97, 1160, 788, 792, 3083]
        ![1158, 14, 800, 1648, 880, 288, 1920, 128, 1536, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![936, 1898, 1000, 252, 1822, 713, 1615, 1582, 1370, 1516, 1286, 2487]
        ![1158, 1122, 1388, 1048, 32, 544, 1152, 1664, 512, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block4. -/
def generatedFifthPermutationPlan5Input4 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![936, 1898, 1000, 252, 1822, 713, 1615, 1582, 1370, 1516, 1286, 2487]
        ![1158, 1122, 1388, 1048, 32, 544, 1152, 1664, 512, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block4 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, false),
      representativeSpinRowsModel
        ![182, 1370, 710, 466, 1326, 2007, 79, 1792, 1898, 1218, 1554, 2487]
        ![1944, 1044, 288, 616, 352, 288, 1984, 0, 512, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1280, 263, 1310, 768, 828, 761, 274, 1871, 1942, 788, 786, 3083]
        ![1944, 878, 1888, 792, 544, 544, 1216, 1536, 1792, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![664, 1744, 122, 864, 46, 453, 1117, 1629, 901, 1566, 394, 3087]
        ![798, 1020, 1260, 2032, 592, 1408, 768, 256, 1024, 512, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1435, 901, 556, 310, 1403, 912, 267, 1035, 1744, 1096, 656, 3087]
        ![1096, 104, 1792, 1688, 384, 1248, 704, 1024, 768, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1648, 613, 597, 806, 2027, 1771, 1691, 1280, 1456, 794, 1248, 3069]
        ![815, 1838, 668, 1376, 2016, 1984, 64, 512, 256, 1024, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1259, 501, 469, 1508, 779, 256, 480, 923, 409, 371, 11, 2255]
        ![292, 156, 1256, 112, 304, 992, 0, 128, 1280, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1179, 1822, 1127, 1277, 768, 523, 912, 635, 16, 1073, 1168, 2191]
        ![1051, 1152, 4, 1152, 496, 896, 128, 0, 256, 0, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1057, 16, 979, 841, 1038, 5, 292, 1487, 1822, 901, 1034, 2191]
        ![416, 682, 224, 568, 1808, 32, 1856, 384, 1280, 0, 0, 0])
  ]

/-- The actual signed model at the start of bounded block5. -/
def generatedFifthPermutationPlan5Input5 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1057, 16, 979, 841, 1038, 5, 292, 1487, 1822, 901, 1034, 2191]
        ![416, 682, 224, 568, 1808, 32, 1856, 384, 1280, 0, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block5 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![491, 469, 501, 624, 1061, 1056, 1216, 271, 781, 1629, 43, 2683]
        ![447, 606, 1468, 1936, 0, 800, 576, 768, 256, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1220, 241, 1999, 402, 1509, 453, 1039, 1280, 10, 1696, 448, 2919]
        ![1056, 2, 1492, 2032, 176, 1536, 640, 1408, 1024, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1706, 10, 1370, 775, 1310, 48, 1940, 1941, 241, 1077, 1949, 2919]
        ![526, 12, 1112, 1024, 32, 704, 1536, 1792, 1280, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![271, 2, 1073, 4, 1065, 1049, 310, 1699, 376, 128, 311, 2048]
        ![128, 848, 740, 184, 704, 832, 0, 1024, 256, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![949, 1942, 852, 980, 1041, 8, 1965, 270, 1975, 312, 56, 3840]
        ![1711, 758, 1912, 272, 1104, 1248, 128, 1920, 256, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![691, 1696, 794, 546, 1948, 1940, 1326, 1056, 1533, 1147, 909, 3083]
        ![305, 662, 188, 1576, 1376, 1856, 320, 1280, 768, 512, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![390, 1533, 882, 586, 1217, 1216, 1359, 1096, 1696, 1043, 693, 3083]
        ![129, 448, 736, 936, 880, 64, 64, 1280, 1536, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![270, 768, 269, 1310, 2034, 818, 564, 1660, 122, 458, 819, 2094]
        ![14, 68, 604, 664, 1408, 1696, 384, 1536, 1280, 512, 0, 0])
  ]

/-- The actual signed model at the start of bounded block6. -/
def generatedFifthPermutationPlan5Input6 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![270, 768, 269, 1310, 2034, 818, 564, 1660, 122, 458, 819, 2094]
        ![14, 68, 604, 664, 1408, 1696, 384, 1536, 1280, 512, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan5Block6 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![432, 122, 713, 1754, 1160, 64, 504, 1464, 768, 526, 1824, 2094]
        ![1822, 798, 1688, 1048, 704, 736, 384, 384, 0, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1096, 738, 1615, 1089, 536, 600, 720, 1896, 1259, 1280, 1680, 2683]
        ![888, 1866, 736, 1248, 1040, 896, 1152, 640, 1536, 0, 1024, 0])
  ]

/-- The bounded blocks are definitionally the entire original literal plan. -/
theorem generatedFifth_permutation_plan5_blocks :
    generatedFifthMonomialPermutationSpinPlan 5 =
      generatedFifthPermutationPlan5Block0 ++
      generatedFifthPermutationPlan5Block1 ++
      generatedFifthPermutationPlan5Block2 ++
      generatedFifthPermutationPlan5Block3 ++
      generatedFifthPermutationPlan5Block4 ++
      generatedFifthPermutationPlan5Block5 ++
      generatedFifthPermutationPlan5Block6 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
