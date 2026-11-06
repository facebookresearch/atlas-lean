/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSegments

/-! Literal bounded portions of original monomial word1, with its complete Parker phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual signed model at the start of bounded block0. -/
def generatedFifthPermutationPlan1Input0 : RepresentativeSpinModel :=
  representativeSpinIdentityModel

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan1Block0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
def generatedFifthPermutationPlan1Input1 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![949, 761, 597, 409, 519, 1533, 1359, 512, 1699, 1696, 609, 2255]
        ![1662, 252, 1500, 472, 0, 800, 512, 512, 1792, 512, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan1Block1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
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
    ((0, true),
      representativeSpinRowsModel
        ![1280, 1021, 349, 1792, 1156, 64, 720, 556, 1197, 525, 331, 2539]
        ![319, 12, 1080, 152, 1568, 512, 1216, 1664, 1024, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1900, 154, 1383, 1898, 207, 143, 1207, 1691, 659, 1698, 1099, 2775]
        ![1085, 512, 1592, 1736, 416, 0, 320, 1920, 0, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1073, 659, 1075, 1598, 710, 466, 1719, 1999, 154, 2038, 1606, 2775]
        ![1497, 514, 724, 1136, 1168, 352, 1088, 1408, 1280, 0, 1024, 0])
  ]

/-- The actual signed model at the start of bounded block2. -/
def generatedFifthPermutationPlan1Input2 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![1073, 659, 1075, 1598, 710, 466, 1719, 1999, 154, 2038, 1606, 2775]
        ![1497, 514, 724, 1136, 1168, 352, 1088, 1408, 1280, 0, 1024, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan1Block2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, false),
      representativeSpinRowsModel
        ![1629, 1008, 349, 1117, 1152, 788, 393, 376, 2032, 525, 27, 2539]
        ![394, 14, 384, 888, 256, 864, 896, 1152, 512, 1536, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1533, 2032, 1789, 1021, 128, 980, 745, 1752, 1008, 1453, 1307, 2539]
        ![331, 14, 740, 1968, 880, 256, 896, 1024, 768, 1536, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![241, 1075, 659, 1854, 102, 946, 1239, 527, 1370, 1366, 230, 2487]
        ![888, 1442, 976, 1752, 736, 960, 704, 896, 1536, 1024, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![12, 1370, 775, 1706, 271, 1359, 727, 923, 1075, 1218, 1355, 2487]
        ![1628, 1440, 92, 160, 1136, 832, 256, 1536, 1024, 512, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1280, 1117, 1789, 768, 1092, 1088, 1744, 332, 781, 1453, 75, 2539]
        ![318, 12, 1084, 1168, 80, 1248, 1408, 1024, 0, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![664, 274, 192, 504, 1039, 4, 263, 1948, 1277, 1533, 723, 2094]
        ![808, 1616, 112, 696, 256, 544, 320, 256, 1024, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![256, 1277, 1719, 1935, 480, 1648, 1259, 491, 274, 906, 1003, 2094]
        ![801, 1890, 740, 1224, 688, 960, 704, 768, 512, 1536, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![912, 390, 1652, 1660, 523, 1936, 512, 1280, 234, 312, 123, 2078]
        ![529, 1266, 992, 1032, 880, 224, 0, 512, 1280, 1024, 0, 0])
  ]

/-- The actual signed model at the start of bounded block3. -/
def generatedFifthPermutationPlan1Input3 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![912, 390, 1652, 1660, 523, 1936, 512, 1280, 234, 312, 123, 2078]
        ![529, 1266, 992, 1032, 880, 224, 0, 512, 1280, 1024, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan1Block3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![466, 234, 1370, 1362, 871, 252, 1838, 1582, 390, 534, 115, 2078]
        ![319, 1100, 380, 464, 1600, 576, 320, 1792, 768, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1792, 1719, 1277, 1771, 710, 570, 161, 1679, 1654, 172, 417, 3328]
        ![801, 254, 1096, 1048, 224, 64, 192, 0, 1024, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![949, 409, 597, 761, 1127, 1629, 143, 1536, 3, 1696, 1697, 3087]
        ![1663, 252, 1496, 464, 16, 1760, 1152, 256, 0, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1699, 3, 1753, 1653, 1533, 672, 356, 652, 409, 556, 1549, 3087]
        ![1165, 160, 164, 168, 672, 352, 704, 384, 0, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1679, 1154, 312, 788, 1363, 2035, 838, 458, 97, 225, 174, 2048]
        ![545, 1570, 1280, 1800, 176, 64, 512, 1792, 512, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![182, 1510, 453, 292, 882, 1153, 1197, 1383, 1092, 81, 1569, 2683]
        ![1107, 1362, 228, 1280, 1008, 1984, 1088, 1536, 768, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![336, 1696, 738, 691, 1509, 356, 1885, 570, 12, 267, 1687, 2971]
        ![331, 1348, 416, 1504, 480, 64, 192, 0, 768, 512, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![263, 12, 1049, 1096, 841, 161, 1743, 1217, 1696, 2032, 1734, 2971]
        ![1761, 82, 1284, 1280, 48, 1536, 1664, 1792, 512, 0, 0, 0])
  ]

/-- The actual signed model at the start of bounded block4. -/
def generatedFifthPermutationPlan1Input4 : RepresentativeSpinModel :=
  representativeSpinRowsModel
        ![263, 12, 1049, 1096, 841, 161, 1743, 1217, 1696, 2032, 1734, 2971]
        ![1761, 82, 1284, 1280, 48, 1536, 1664, 1792, 512, 0, 0, 0]

/-- At most eight actual original source letters and their full signed models. -/
def generatedFifthPermutationPlan1Block4 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![1383, 523, 525, 1533, 1160, 1065, 1487, 270, 659, 1698, 1985, 2397]
        ![537, 174, 1192, 104, 1920, 1536, 320, 768, 256, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![1073, 659, 963, 1075, 1040, 48, 128, 192, 523, 1900, 49, 2397]
        ![1039, 14, 1036, 1024, 672, 480, 896, 1792, 512, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1217, 610, 1220, 936, 16, 32, 1088, 1152, 256, 1536, 1024, 3328]
        ![1281, 928, 1284, 616, 464, 1952, 960, 640, 1792, 0, 0, 0])
  ]

/-- The bounded blocks are definitionally the entire original literal plan. -/
theorem generatedFifth_permutation_plan1_blocks :
    generatedFifthMonomialPermutationSpinPlan 1 =
      generatedFifthPermutationPlan1Block0 ++
      generatedFifthPermutationPlan1Block1 ++
      generatedFifthPermutationPlan1Block2 ++
      generatedFifthPermutationPlan1Block3 ++
      generatedFifthPermutationPlan1Block4 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
