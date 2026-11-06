/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit intermediate spin models for each compact representative-word edge. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlan

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 20000

/-- Binary row data converted into the two matrices of a full spin model. -/
def representativeSpinRowsModel (P M : Fin 12 → Fin 4096) : RepresentativeSpinModel :=
  ⟨representativeMatrix P, representativeMatrix M⟩

/-- Exact signed-node models; inverse phases are retained explicitly. -/
def representativeNodeSpinModel (letter : RepresentativeNodeLetter) : RepresentativeSpinModel :=
  if letter.2 then
    representativeSpinRowsModel (representativeNodeInverseRows letter.1)
      (representativeNodeInversePhaseRows letter.1)
  else representativeSpinRowsModel (representativeNodeCoordinateRows letter.1)
    (representativeNodePhaseRows letter.1)

/-- The identity model at the start of a derived node plan. -/
def representativeSpinIdentityModel : RepresentativeSpinModel := ⟨1, 0⟩

/-- The actual cocode sign at the start of a corrected target plan. -/
def representativePermutationStartModel (n : Fin 83) : RepresentativeSpinModel :=
  ⟨1, Matrix.diagonal (golayLabelCoefficients (representativePermutationCorrection n))⟩

/-- Intermediate full spin models along each compact defining node word. -/
def representativeNodeSpinPlan : Fin 15 → RepresentativeSpinPlan RepresentativeNodeLetter :=
  ![
    [],
    [],
    [
      ((0, false),
        representativeSpinRowsModel
          ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
          ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
          ![527, 14, 12, 8, 0, 0, 0, 128, 256, 1024, 1024, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
          ![556, 2, 208, 112, 0, 512, 0, 640, 768, 512, 1024, 0])],
    [
      ((0, false),
        representativeSpinRowsModel
          ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
          ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![209, 1218, 1743, 692, 177, 1152, 1056, 97, 828, 332, 1184, 3079]
          ![1085, 1696, 1236, 520, 1312, 1440, 1920, 0, 256, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![624, 828, 912, 2027, 1871, 783, 270, 1342, 1218, 1043, 219, 3079]
          ![513, 1038, 216, 1240, 1200, 1088, 1152, 128, 256, 1536, 0, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![512, 1495, 1935, 1838, 1940, 1088, 1509, 1072, 1654, 1147, 731, 2733]
          ![709, 0, 1748, 1544, 800, 1280, 448, 1536, 512, 0, 0, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![1, 1752, 4, 8, 1359, 980, 1771, 469, 756, 161, 730, 2048]
          ![1519, 160, 628, 160, 800, 1952, 448, 1024, 512, 0, 0, 0])],
    [
      ((1, false),
        representativeSpinRowsModel
          ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
          ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![768, 1975, 519, 523, 1056, 949, 1510, 182, 756, 192, 699, 2048]
          ![558, 92, 444, 0, 320, 672, 1984, 1536, 512, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![564, 756, 1648, 1660, 355, 933, 1218, 1217, 1975, 1207, 695, 2048]
          ![1704, 174, 444, 1712, 128, 96, 512, 512, 1280, 512, 0, 0])],
    [
      ((3, false),
        representativeSpinRowsModel
          ![1, 1752, 4, 8, 1359, 980, 1771, 469, 756, 161, 730, 2048]
          ![1519, 160, 628, 160, 800, 1952, 448, 1024, 512, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![597, 756, 1660, 1648, 355, 710, 1453, 1965, 1752, 1753, 726, 2048]
          ![1701, 160, 220, 2008, 128, 64, 576, 512, 1024, 512, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![597, 284, 1660, 1648, 270, 1310, 536, 402, 256, 1854, 318, 2048]
          ![287, 1938, 1772, 736, 656, 96, 0, 256, 1536, 1536, 0, 0])],
    [
      ((1, false),
        representativeSpinRowsModel
          ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
          ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![12, 8, 519, 263, 806, 371, 794, 691, 782, 3, 1795, 2048]
          ![818, 240, 700, 376, 512, 256, 768, 896, 0, 0, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![12, 1160, 519, 263, 1043, 901, 1753, 906, 504, 972, 899, 2048]
          ![984, 660, 1744, 1944, 832, 928, 1472, 1920, 1024, 1024, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![768, 1615, 519, 523, 1822, 323, 1752, 332, 756, 972, 835, 2048]
          ![272, 82, 1708, 1056, 144, 64, 1152, 1408, 1024, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![312, 756, 1156, 1160, 933, 355, 1216, 1999, 1615, 1359, 847, 2048]
          ![1890, 160, 984, 2000, 144, 832, 512, 256, 1024, 512, 0, 0])],
    [
      ((2, false),
        representativeSpinRowsModel
          ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
          ![556, 2, 208, 112, 0, 512, 0, 640, 768, 512, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![12, 1156, 4, 5, 1822, 901, 1207, 393, 761, 172, 130, 2048]
          ![45, 174, 1048, 1080, 544, 1952, 192, 1152, 256, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1, 1057, 4, 8, 1043, 32, 1975, 556, 756, 172, 35, 2048]
          ![173, 172, 1376, 2024, 656, 1984, 0, 1152, 0, 0, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1, 271, 4, 8, 332, 980, 284, 889, 256, 525, 1293, 2048]
          ![332, 2, 228, 176, 768, 256, 768, 256, 256, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![781, 256, 775, 779, 323, 274, 214, 122, 271, 270, 1281, 2048]
          ![122, 242, 332, 272, 0, 256, 0, 256, 256, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![12, 8, 775, 10, 466, 906, 838, 738, 526, 270, 1806, 2048]
          ![0, 254, 468, 744, 784, 800, 576, 256, 512, 512, 0, 0])],
    [
      ((4, false),
        representativeSpinRowsModel
          ![564, 756, 1648, 1660, 355, 933, 1218, 1217, 1975, 1207, 695, 2048]
          ![1704, 174, 444, 1712, 128, 96, 512, 512, 1280, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![12, 1660, 1456, 1160, 1059, 841, 838, 1509, 1615, 1359, 847, 2048]
          ![229, 616, 528, 856, 144, 64, 1472, 1792, 256, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![1, 1696, 1936, 1464, 288, 800, 64, 0, 768, 512, 1024, 0])],
    [
      ((5, false),
        representativeSpinRowsModel
          ![597, 284, 1660, 1648, 270, 1310, 536, 402, 256, 1854, 318, 2048]
          ![287, 1938, 1772, 736, 656, 96, 0, 256, 1536, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![949, 624, 556, 332, 1040, 270, 1698, 1706, 256, 1854, 318, 2048]
          ![286, 160, 1500, 464, 256, 32, 512, 0, 256, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1045, 1648, 1756, 1468, 16, 1342, 610, 458, 256, 782, 1294, 2048]
          ![1311, 80, 1304, 272, 16, 736, 960, 640, 1280, 512, 0, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![501, 1516, 652, 624, 1342, 1326, 1464, 1362, 256, 782, 1294, 2048]
          ![1310, 1890, 1576, 544, 128, 416, 448, 896, 1536, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![241, 1218, 852, 936, 1040, 1056, 1088, 1152, 256, 512, 1024, 2048]
          ![1073, 2, 1940, 1896, 688, 320, 704, 384, 1024, 1536, 1024, 0])],
    [
      ((7, false),
        representativeSpinRowsModel
          ![12, 8, 775, 10, 466, 906, 838, 738, 526, 270, 1806, 2048]
          ![0, 254, 468, 744, 784, 800, 576, 256, 512, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![81, 501, 1822, 1043, 710, 355, 1698, 1702, 1975, 1207, 695, 2048]
          ![695, 160, 292, 1464, 752, 224, 640, 768, 256, 1536, 0, 0]),
      ((7, true),
        representativeSpinRowsModel
          ![92, 1510, 420, 501, 432, 1744, 480, 1648, 256, 512, 1024, 2048]
          ![1040, 2, 1504, 1464, 160, 64, 192, 128, 1792, 0, 0, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![409, 371, 1061, 225, 1744, 1888, 32, 1072, 256, 512, 1024, 2048]
          ![1056, 1362, 0, 1456, 736, 384, 960, 512, 0, 1024, 0, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![312, 546, 1153, 788, 1888, 432, 1216, 1088, 256, 512, 1024, 2048]
          ![0, 1698, 1940, 1464, 32, 0, 256, 768, 1536, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1896, 1698, 1057, 1508, 864, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 448, 896, 768, 0, 1024, 0])],
    [
      ((0, false),
        representativeSpinRowsModel
          ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
          ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![209, 1218, 1743, 692, 177, 1152, 1056, 97, 828, 332, 1184, 3079]
          ![1085, 1696, 1236, 520, 1312, 1440, 1920, 0, 256, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1072, 3, 1753, 1941, 1216, 64, 48, 81, 652, 534, 1137, 3328]
          ![1281, 450, 724, 1880, 592, 352, 384, 768, 1536, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![154, 652, 252, 432, 1615, 1679, 597, 1652, 3, 1075, 1341, 3328]
          ![879, 1198, 1244, 216, 1536, 1568, 0, 128, 1024, 0, 1024, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![1147, 2027, 1743, 1566, 882, 192, 841, 1057, 1942, 332, 326, 3079]
          ![595, 642, 1648, 96, 368, 896, 704, 512, 1536, 512, 0, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![161, 356, 1935, 1423, 564, 946, 1383, 1896, 852, 209, 487, 2733]
          ![150, 886, 524, 480, 656, 320, 384, 1792, 768, 1536, 0, 0]),
      ((0, true),
        representativeSpinRowsModel
          ![808, 420, 1092, 1096, 979, 390, 1679, 527, 1999, 512, 719, 2048]
          ![1746, 82, 696, 1720, 656, 96, 576, 256, 1280, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![808, 980, 1092, 1096, 271, 1752, 781, 2032, 145, 161, 191, 2048]
          ![547, 254, 1868, 832, 656, 352, 512, 512, 1024, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![12, 1045, 1092, 1900, 1216, 2034, 1510, 1754, 949, 161, 826, 2048]
          ![19, 240, 404, 1280, 272, 320, 0, 768, 1536, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![788, 949, 252, 980, 864, 586, 838, 610, 1045, 1049, 18, 2048]
          ![827, 1096, 1792, 504, 784, 512, 832, 768, 1280, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![788, 1435, 252, 980, 1224, 692, 1040, 1465, 1259, 828, 1596, 2048]
          ![164, 532, 1384, 960, 512, 1184, 640, 1664, 1024, 1536, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![808, 1639, 252, 1000, 1220, 376, 1056, 1653, 1239, 828, 1340, 2048]
          ![89, 296, 968, 1688, 1088, 288, 1472, 256, 1024, 1024, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![643, 1065, 949, 161, 818, 1216, 1897, 1753, 1147, 912, 1424, 2048]
          ![785, 1792, 1536, 1696, 1600, 512, 768, 0, 1792, 1024, 1024, 0]),
      ((7, true),
        representativeSpinRowsModel
          ![1660, 1160, 1706, 1065, 779, 267, 672, 906, 1435, 624, 1136, 2048]
          ![539, 114, 1536, 1696, 512, 640, 576, 0, 512, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![781, 1043, 1059, 1696, 912, 1259, 1362, 402, 1435, 1936, 400, 2048]
          ![1230, 204, 1692, 352, 1216, 1600, 896, 1408, 1536, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1088, 8, 1057, 1698, 92, 828, 1360, 710, 1743, 1220, 708, 2048]
          ![592, 524, 172, 632, 1712, 1312, 320, 896, 1024, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![901, 1043, 48, 691, 1259, 912, 1370, 274, 256, 779, 1291, 2048]
          ![1399, 372, 1692, 1080, 656, 128, 512, 256, 0, 1536, 1024, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![252, 720, 808, 1896, 912, 1915, 1699, 1217, 256, 779, 1291, 2048]
          ![1750, 1094, 1688, 1400, 304, 224, 320, 128, 0, 1536, 0, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![332, 600, 536, 1744, 1915, 1259, 2034, 979, 256, 779, 1291, 2048]
          ![935, 310, 1692, 1032, 64, 0, 576, 768, 256, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![214, 691, 1706, 610, 1936, 1504, 672, 2032, 256, 512, 1024, 2048]
          ![1041, 1696, 1648, 0, 112, 224, 192, 128, 512, 1536, 1024, 0]),
      ((8, true),
        representativeSpinRowsModel
          ![756, 161, 1154, 600, 1504, 624, 1216, 1088, 256, 512, 1024, 2048]
          ![1057, 0, 1652, 1752, 688, 352, 448, 768, 1024, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1888, 16, 32, 896, 640, 768, 512, 0, 0]),
      ((10, true),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 16, 32, 576, 256, 0, 512, 1024, 0])],
    [
      ((10, false),
        representativeSpinRowsModel
          ![1896, 1698, 1057, 1508, 864, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 448, 896, 768, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 16, 0, 704, 384, 768, 0, 1024, 0]),
      ((10, true),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 16, 0, 768, 512, 0, 0, 0, 0])],
    [
      ((9, false),
        representativeSpinRowsModel
          ![241, 1218, 852, 936, 1040, 1056, 1088, 1152, 256, 512, 1024, 2048]
          ![1073, 2, 1940, 1896, 688, 320, 704, 384, 1024, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1218, 241, 936, 852, 336, 672, 1088, 1152, 256, 512, 1024, 2048]
          ![1073, 2, 1940, 1896, 672, 352, 128, 128, 0, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1456, 16, 32, 704, 384, 512, 0, 1024, 0])],
    [
      ((10, false),
        representativeSpinRowsModel
          ![1896, 1698, 1057, 1508, 864, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 448, 896, 768, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1464, 1652, 1073, 1696, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1456, 16, 0, 640, 256, 512, 0, 1024, 0]),
      ((10, true),
        representativeSpinRowsModel
          ![1940, 1752, 1041, 1362, 912, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 0, 0, 896, 640, 768, 0, 1024, 0])]]

/-- Intermediate spin models for source permutation 960. -/
def representativePermutationSpinPlan960 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((14, false),
        representativeSpinRowsModel
          ![1940, 1752, 1041, 1362, 912, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1744, 0, 0, 960, 640, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1464, 1652, 1073, 1696, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1456, 16, 0, 704, 256, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 8, 2, 4, 48, 16, 128, 192, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 0, 32, 64, 0, 256, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![546, 610, 1696, 1702, 409, 979, 1096, 1089, 2027, 1259, 747, 2048]
          ![1748, 494, 1772, 216, 80, 224, 576, 0, 1024, 0, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![610, 546, 1702, 1696, 570, 889, 1096, 1089, 2027, 1259, 747, 2048]
          ![311, 484, 1772, 1072, 80, 224, 320, 0, 0, 1024, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![782, 775, 779, 781, 154, 252, 192, 128, 527, 271, 1807, 2048]
          ![0, 192, 128, 64, 0, 0, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1200. -/
def representativePermutationSpinPlan1200 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((14, false),
        representativeSpinRowsModel
          ![1940, 1752, 1041, 1362, 912, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 0, 32, 896, 640, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1464, 1652, 1073, 1696, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 16, 32, 640, 256, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![102, 1948, 949, 980, 1360, 1696, 1504, 1648, 256, 512, 1024, 2048]
          ![1057, 2034, 1940, 0, 96, 224, 128, 128, 1536, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2035, 1753, 1217, 1509, 1008, 1360, 32, 48, 256, 512, 1024, 2048]
          ![1, 2032, 1508, 1744, 544, 288, 64, 0, 512, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![97, 113, 128, 420, 1370, 1362, 713, 995, 1147, 1915, 379, 2048]
          ![791, 372, 156, 664, 48, 1344, 512, 512, 0, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![113, 97, 420, 128, 1000, 458, 713, 995, 1147, 1915, 379, 2048]
          ![316, 1062, 156, 1216, 272, 32, 64, 384, 1536, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1277, 1495, 1771, 1999, 1896, 252, 48, 32, 526, 270, 1806, 2048]
          ![0, 2032, 1472, 1728, 32, 0, 0, 0, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1920. -/
def representativePermutationSpinPlan1920 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 0, 32, 576, 256, 0, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 16, 32, 256, 768, 256, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 0, 0, 960, 512, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1057, 1698, 1508, 1896, 1040, 32, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 192, 0, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![8, 2, 1, 4, 864, 432, 192, 64, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 0, 32, 256, 896, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1652, 2034, 1464, 1073, 624, 1936, 128, 192, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 0, 32, 960, 512, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![980, 946, 1096, 97, 1648, 912, 1152, 1216, 256, 512, 1024, 2048]
          ![1057, 2034, 1940, 0, 864, 704, 704, 384, 1024, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![113, 738, 1092, 664, 1040, 1056, 64, 1152, 256, 512, 1024, 2048]
          ![1073, 1698, 0, 1744, 496, 896, 896, 512, 0, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![936, 692, 1220, 536, 1941, 2035, 192, 1935, 527, 271, 1807, 2048]
          ![1459, 1650, 328, 1344, 432, 800, 832, 0, 512, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1153, 756, 145, 356, 154, 252, 1999, 128, 527, 271, 1807, 2048]
          ![1924, 600, 896, 464, 96, 128, 128, 768, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 7722. -/
def representativePermutationSpinPlan7722 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 0, 16, 32, 512, 384, 256, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 0, 32, 320, 896, 0, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 16, 0, 896, 640, 768, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1057, 1698, 1508, 1896, 1040, 32, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1508, 1896, 16, 0, 128, 128, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![8, 2, 1, 4, 864, 432, 192, 64, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 16, 32, 320, 768, 0, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1065, 979, 949, 97, 720, 864, 32, 1072, 256, 512, 1024, 2048]
          ![1056, 2032, 1936, 0, 96, 224, 384, 768, 256, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![949, 97, 1065, 979, 1504, 1648, 32, 1072, 256, 512, 1024, 2048]
          ![1056, 2032, 1940, 8, 608, 480, 448, 768, 0, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![761, 1059, 597, 161, 720, 1888, 32, 1072, 256, 512, 1024, 2048]
          ![1056, 0, 1648, 1744, 432, 832, 704, 384, 1024, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1509, 501, 912, 356, 154, 252, 1075, 745, 527, 271, 1807, 2048]
          ![1912, 422, 628, 800, 608, 416, 384, 384, 1536, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![420, 1504, 534, 182, 1999, 1935, 1754, 1075, 527, 271, 1807, 2048]
          ![104, 4, 1024, 800, 416, 768, 256, 512, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 19227. -/
def representativePermutationSpinPlan19227 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 0, 16, 32, 576, 256, 0, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 0, 32, 256, 768, 256, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1362, 1041, 1752, 1940, 336, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1362, 1936, 1744, 0, 32, 640, 384, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 1081, 1516, 1160, 2032, 336, 720, 864, 256, 512, 1024, 2048]
          ![1073, 1360, 1508, 0, 608, 448, 704, 256, 512, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1516, 1160, 1370, 1081, 1936, 480, 720, 864, 256, 512, 1024, 2048]
          ![1073, 1362, 1504, 0, 352, 960, 896, 512, 768, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1706, 1049, 1660, 1224, 2032, 1360, 720, 864, 256, 512, 1024, 2048]
          ![1041, 1696, 1652, 0, 608, 480, 704, 256, 768, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1756, 1900, 1648, 1220, 1075, 1510, 425, 794, 527, 271, 1807, 2048]
          ![148, 600, 1632, 864, 672, 256, 0, 0, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 22080. -/
def representativePermutationSpinPlan22080 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 0, 0, 576, 384, 0, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 16, 0, 256, 896, 256, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1464, 0, 32, 960, 640, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1057, 1698, 1508, 1896, 1040, 32, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1896, 0, 32, 192, 128, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![8, 2, 1, 4, 864, 432, 192, 64, 256, 512, 1024, 2048]
          ![1, 2, 0, 8, 0, 0, 256, 768, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1652, 2034, 1464, 1073, 624, 1936, 128, 192, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1456, 0, 0, 960, 640, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1660, 1706, 1049, 1224, 1504, 624, 432, 720, 256, 512, 1024, 2048]
          ![1040, 1698, 1652, 0, 352, 960, 960, 512, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1065, 1096, 1948, 2042, 1072, 1040, 432, 720, 256, 512, 1024, 2048]
          ![1057, 2034, 1936, 0, 112, 192, 384, 896, 256, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1077, 1366, 2038, 1936, 1326, 1310, 458, 936, 256, 782, 1294, 2048]
          ![1342, 310, 1332, 184, 16, 992, 960, 640, 1280, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![581, 912, 1654, 214, 48, 1326, 1160, 882, 256, 782, 1294, 2048]
          ![1343, 534, 1556, 1944, 832, 768, 640, 384, 1536, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![912, 581, 214, 1654, 1464, 1362, 1160, 882, 256, 782, 1294, 2048]
          ![1343, 1948, 664, 16, 592, 512, 896, 512, 0, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![376, 536, 1218, 610, 1509, 1363, 192, 1423, 256, 783, 1295, 2048]
          ![1892, 904, 1696, 1920, 608, 288, 64, 256, 512, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![980, 564, 1090, 738, 1897, 2035, 64, 1935, 768, 271, 1807, 2048]
          ![1512, 388, 1412, 1704, 752, 480, 0, 896, 768, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1153, 756, 356, 145, 102, 252, 1871, 128, 768, 271, 1807, 2048]
          ![1924, 600, 896, 464, 96, 128, 128, 768, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 30720. -/
def representativePermutationSpinPlan30720 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 16, 32, 832, 640, 0, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1744, 16, 32, 192, 0, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 2034, 1073, 1652, 1888, 432, 192, 64, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1456, 0, 32, 448, 768, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![425, 1043, 501, 81, 1744, 1888, 1056, 1072, 256, 512, 1024, 2048]
          ![1041, 0, 1504, 1464, 432, 864, 640, 256, 1024, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 323, 713, 901, 64, 128, 16, 1056, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 0, 32, 128, 128, 768, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![225, 371, 409, 1061, 1088, 1152, 1040, 32, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1464, 480, 896, 896, 512, 1024, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![808, 252, 1900, 720, 1487, 1423, 613, 1043, 256, 783, 1295, 2048]
          ![1939, 1744, 972, 1984, 304, 960, 512, 128, 768, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![664, 1744, 828, 172, 64, 1487, 979, 2038, 256, 783, 1295, 2048]
          ![83, 274, 12, 1024, 928, 640, 512, 896, 256, 512, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1744, 664, 172, 828, 659, 310, 979, 2038, 256, 783, 1295, 2048]
          ![142, 204, 728, 2008, 432, 896, 64, 384, 1792, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1075, 3, 1510, 1654, 8, 1940, 672, 1789, 256, 1453, 941, 2048]
          ![1334, 1966, 304, 600, 1840, 2016, 640, 384, 1024, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![234, 906, 182, 806, 1041, 4, 2032, 1277, 768, 1965, 429, 2048]
          ![275, 254, 120, 1136, 784, 768, 64, 768, 1024, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1040, 1153, 1653, 1509, 794, 1702, 154, 102, 768, 271, 1807, 2048]
          ![1822, 204, 24, 64, 352, 896, 896, 512, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 49920. -/
def representativePermutationSpinPlan49920 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 8, 0, 0, 832, 640, 256, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 16, 32, 448, 768, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 1940, 1752, 1362, 1056, 1072, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1744, 0, 0, 192, 128, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1508, 1057, 1896, 2032, 1360, 128, 192, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1888, 16, 0, 704, 384, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![691, 613, 1049, 209, 672, 2032, 1072, 16, 256, 512, 1024, 2048]
          ![1041, 1696, 1648, 8, 368, 960, 448, 768, 1024, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 901, 323, 713, 192, 64, 1056, 1072, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1752, 16, 0, 192, 128, 768, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1153, 1941, 1699, 1465, 1216, 1088, 32, 48, 256, 512, 1024, 2048]
          ![0, 1696, 1940, 1456, 48, 32, 64, 0, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1218, 1754, 1466, 1696, 1423, 1359, 889, 613, 256, 783, 1295, 2048]
          ![293, 1482, 224, 448, 608, 288, 576, 0, 1024, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1942, 2032, 1154, 1510, 1081, 1706, 284, 889, 256, 783, 1295, 2048]
          ![82, 2016, 492, 976, 864, 544, 0, 128, 1792, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1310, 1915, 1423, 1259, 1744, 1224, 154, 252, 526, 1, 1537, 2048]
          ![1823, 860, 528, 288, 96, 384, 384, 768, 1536, 1536, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1965, 1117, 1487, 1342, 1059, 161, 154, 252, 526, 1, 1537, 2048]
          ![1986, 80, 880, 976, 352, 640, 384, 512, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 130560. -/
def representativePermutationSpinPlan130560 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 8, 16, 0, 832, 640, 256, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1464, 0, 32, 448, 768, 768, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1698, 1057, 1896, 1508, 1360, 672, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 32, 704, 256, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![794, 1465, 556, 312, 2032, 1360, 1744, 1888, 256, 512, 1024, 2048]
          ![1, 1698, 1940, 1456, 288, 768, 832, 640, 1024, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 393, 586, 972, 128, 192, 432, 1744, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1464, 0, 32, 384, 768, 768, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![664, 745, 122, 1756, 1152, 1216, 1456, 720, 256, 512, 1024, 2048]
          ![1072, 1698, 0, 1752, 480, 928, 704, 256, 1280, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![466, 806, 1366, 1008, 1359, 1487, 92, 1465, 256, 783, 1295, 2048]
          ![2041, 1860, 832, 1648, 304, 960, 256, 0, 768, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![882, 2032, 102, 534, 128, 1359, 761, 1061, 256, 783, 1295, 2048]
          ![184, 1028, 0, 304, 608, 288, 512, 896, 0, 0, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1702, 122, 310, 838, 564, 113, 1059, 161, 526, 1, 1537, 2048]
          ![83, 1196, 172, 1184, 336, 352, 768, 0, 256, 1536, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1965, 1008, 659, 610, 154, 252, 1059, 161, 526, 1, 1537, 2048]
          ![1986, 80, 880, 976, 352, 640, 384, 512, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 744960. -/
def representativePermutationSpinPlan744960 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 0, 16, 32, 512, 256, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 16, 32, 960, 640, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1041, 1940, 1362, 1456, 720, 128, 192, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 16, 0, 384, 768, 768, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1509, 534, 292, 1888, 1456, 1648, 1936, 256, 512, 1024, 2048]
          ![1, 2034, 1508, 1752, 560, 256, 576, 256, 1024, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 453, 652, 838, 192, 64, 480, 1648, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1888, 16, 0, 896, 640, 768, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![756, 597, 172, 1654, 1216, 1088, 1504, 624, 256, 512, 1024, 2048]
          ![1056, 0, 1648, 1752, 672, 320, 384, 768, 1280, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![376, 794, 1466, 864, 1423, 1359, 182, 1509, 256, 783, 1295, 2048]
          ![1893, 904, 1700, 1920, 608, 288, 0, 256, 768, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![409, 1456, 312, 425, 2038, 298, 1363, 182, 256, 783, 1295, 2048]
          ![2018, 1936, 1048, 488, 688, 384, 512, 896, 512, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![225, 852, 692, 1217, 1756, 2038, 1359, 192, 256, 783, 1295, 2048]
          ![1028, 616, 0, 936, 224, 64, 704, 768, 768, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![145, 1310, 613, 1040, 12, 1900, 980, 97, 2027, 1508, 996, 2048]
          ![1903, 656, 112, 1384, 240, 576, 512, 384, 1280, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1653, 1147, 613, 756, 1220, 1061, 504, 808, 271, 1508, 228, 2048]
          ![735, 1908, 584, 1944, 1600, 512, 1088, 1536, 1792, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1259, 271, 1423, 1310, 432, 761, 1466, 1218, 1147, 526, 117, 2048]
          ![1639, 1196, 156, 160, 400, 32, 1920, 768, 256, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![145, 756, 1423, 356, 1744, 536, 1696, 1059, 1, 526, 1537, 2048]
          ![982, 324, 8, 304, 608, 384, 384, 768, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 1351680. -/
def representativePermutationSpinPlan1351680 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 16, 32, 768, 512, 0, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1045, 889, 995, 145, 624, 912, 16, 1056, 256, 512, 1024, 2048]
          ![1040, 2032, 0, 1896, 240, 128, 896, 512, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1702, 122, 738, 659, 480, 624, 1360, 672, 256, 512, 1024, 2048]
          ![1072, 1696, 4, 1752, 752, 416, 704, 384, 512, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![756, 145, 177, 192, 267, 1259, 371, 570, 256, 1179, 667, 2048]
          ![2036, 222, 232, 1072, 1248, 1920, 1728, 896, 1280, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![600, 64, 1156, 1160, 3, 1089, 841, 371, 256, 1179, 667, 2048]
          ![828, 1076, 1692, 920, 144, 64, 768, 128, 0, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![269, 271, 263, 267, 332, 980, 16, 48, 256, 782, 1294, 2048]
          ![1, 2, 48, 40, 512, 256, 0, 0, 256, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![145, 177, 1160, 1156, 710, 480, 1057, 1059, 1197, 1699, 163, 2048]
          ![263, 1226, 1436, 912, 128, 832, 64, 128, 1024, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![783, 271, 8, 4, 980, 332, 161, 643, 525, 3, 1539, 2048]
          ![665, 980, 168, 552, 528, 288, 512, 0, 512, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![271, 783, 4, 8, 376, 972, 161, 643, 525, 3, 1539, 2048]
          ![692, 376, 552, 160, 512, 256, 512, 512, 512, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![526, 525, 519, 523, 122, 172, 192, 128, 783, 512, 1551, 2048]
          ![0, 128, 64, 192, 0, 0, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1394880. -/
def representativePermutationSpinPlan1394880 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((8, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![0, 1698, 1936, 1464, 304, 768, 0, 0, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 570, 808, 284, 32, 48, 1744, 864, 256, 512, 1024, 2048]
          ![1, 1362, 1648, 1896, 816, 544, 0, 0, 768, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![713, 906, 1752, 332, 1056, 1072, 720, 1888, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1752, 784, 512, 128, 128, 768, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![225, 692, 852, 1216, 1310, 1342, 1900, 458, 256, 782, 1294, 2048]
          ![1327, 986, 4, 752, 480, 608, 192, 128, 512, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![818, 1487, 292, 536, 1660, 756, 1900, 458, 256, 782, 1294, 2048]
          ![1, 398, 416, 904, 288, 0, 512, 256, 1536, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1698, 4, 1508, 1752, 613, 806, 1639, 154, 1435, 1941, 405, 2048]
          ![2, 444, 1072, 768, 720, 1280, 768, 768, 0, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1152, 1088, 1362, 8, 241, 469, 1639, 154, 1435, 1941, 405, 2048]
          ![3, 218, 332, 1864, 848, 1600, 256, 128, 256, 512, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![526, 1435, 519, 1885, 298, 828, 512, 1999, 1088, 192, 1231, 2048]
          ![1536, 2000, 1488, 1728, 1920, 704, 640, 512, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1415040. -/
def representativePermutationSpinPlan1415040 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 16, 32, 512, 384, 256, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 0, 0, 128, 128, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1362, 1041, 1940, 1888, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 16, 32, 384, 896, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![745, 659, 1077, 113, 720, 1888, 1056, 48, 256, 512, 1024, 2048]
          ![1073, 1696, 0, 1752, 736, 416, 960, 512, 1024, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![841, 643, 453, 1057, 1744, 864, 32, 1072, 256, 512, 1024, 2048]
          ![1057, 1698, 1508, 1888, 768, 512, 128, 0, 1792, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1900, 2038, 1156, 1045, 1456, 1744, 480, 624, 256, 512, 1024, 2048]
          ![1041, 2034, 4, 1896, 992, 672, 384, 896, 512, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1464, 1057, 1041, 1152, 1639, 2007, 933, 310, 256, 775, 1287, 2048]
          ![185, 92, 232, 1200, 672, 928, 256, 896, 1024, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1216, 1896, 1362, 1653, 1153, 659, 933, 256, 775, 1287, 2048]
          ![299, 346, 332, 1640, 432, 128, 0, 768, 1536, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1915, 1359, 1117, 1639, 2042, 1160, 32, 16, 256, 782, 1294, 2048]
          ![0, 1378, 1648, 1904, 800, 544, 0, 0, 512, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1057, 1041, 1362, 1896, 1948, 1456, 113, 581, 523, 5, 1541, 2048]
          ![28, 1836, 928, 1880, 80, 96, 512, 640, 512, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1152, 1216, 1464, 2034, 2007, 906, 113, 581, 523, 5, 1541, 2048]
          ![547, 1994, 1004, 1992, 848, 352, 256, 128, 768, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![526, 523, 1533, 1975, 284, 570, 1871, 512, 1216, 64, 1103, 2048]
          ![1536, 1392, 1600, 1904, 1408, 1984, 640, 0, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1457280. -/
def representativePermutationSpinPlan1457280 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1464, 0, 0, 640, 384, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 384, 896, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 4, 8, 2, 32, 48, 192, 64, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 0, 32, 0, 0, 256, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1652, 1073, 1464, 1008, 1360, 128, 192, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 0, 32, 704, 384, 512, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![274, 564, 1089, 808, 2032, 336, 1152, 1216, 256, 512, 1024, 2048]
          ![1, 1362, 1652, 1888, 32, 0, 576, 256, 1792, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![504, 420, 1090, 81, 1744, 1888, 64, 1152, 256, 512, 1024, 2048]
          ![1041, 0, 1508, 1456, 688, 320, 896, 640, 0, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1160, 356, 466, 177, 720, 864, 1088, 128, 256, 512, 1024, 2048]
          ![1072, 1362, 1504, 8, 880, 736, 128, 128, 0, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1, 1698, 1362, 1073, 1466, 972, 192, 1871, 1743, 1487, 975, 2048]
          ![1266, 242, 648, 328, 2032, 1984, 1472, 1536, 768, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![768, 1743, 1598, 1885, 1495, 172, 161, 1059, 1698, 1699, 684, 2048]
          ![642, 0, 880, 976, 1504, 1984, 1408, 1792, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 1461120. -/
def representativePermutationSpinPlan1461120 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 0, 0, 512, 256, 256, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 16, 0, 320, 768, 0, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1362, 1041, 1752, 1940, 336, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1752, 16, 0, 704, 384, 768, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1652, 1073, 2034, 1464, 1504, 624, 192, 64, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1464, 0, 0, 896, 640, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![8, 1, 4, 2, 432, 720, 128, 192, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 16, 32, 256, 768, 256, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1660, 613, 214, 692, 864, 432, 624, 1936, 256, 512, 1024, 2048]
          ![1040, 1698, 1648, 0, 368, 992, 960, 640, 768, 512, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![613, 1660, 692, 214, 16, 1056, 624, 1936, 256, 512, 1024, 2048]
          ![1040, 1698, 1648, 0, 624, 448, 448, 768, 1024, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![692, 214, 613, 1660, 1152, 192, 624, 1936, 256, 512, 1024, 2048]
          ![1041, 1698, 1648, 0, 880, 704, 640, 384, 1024, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1061, 453, 48, 1065, 466, 1153, 310, 852, 1239, 2007, 471, 2048]
          ![106, 1512, 952, 1488, 240, 1696, 1664, 512, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![97, 409, 1056, 1057, 390, 995, 310, 852, 1239, 2007, 471, 2048]
          ![1147, 1514, 1372, 96, 592, 1728, 1024, 512, 768, 0, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1, 1057, 1752, 1464, 1706, 1516, 1935, 1999, 1615, 1359, 847, 2048]
          ![1128, 710, 388, 104, 48, 1888, 1664, 896, 768, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![768, 1615, 1975, 1239, 1220, 1504, 1154, 1696, 1057, 1056, 47, 2048]
          ![1838, 940, 1000, 0, 832, 1728, 1024, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1481280. -/
def representativePermutationSpinPlan1481280 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 0, 32, 576, 256, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1888, 0, 32, 896, 640, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1510, 1043, 1466, 1090, 1936, 480, 672, 1008, 256, 512, 1024, 2048]
          ![1040, 0, 1504, 1464, 432, 864, 896, 512, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1753, 536, 298, 1648, 1936, 1888, 1456, 256, 512, 1024, 2048]
          ![0, 2032, 1508, 1752, 544, 288, 576, 256, 1280, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![536, 298, 828, 1753, 192, 1088, 1888, 1456, 256, 512, 1024, 2048]
          ![0, 2032, 1504, 1752, 48, 32, 256, 768, 768, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1156, 1061, 5, 1504, 1487, 271, 1049, 1370, 256, 1871, 335, 2048]
          ![1460, 1946, 436, 592, 448, 128, 832, 1920, 512, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![263, 1065, 1948, 2042, 1152, 64, 1366, 1045, 256, 1871, 335, 2048]
          ![160, 818, 2000, 0, 2032, 640, 1088, 1920, 1024, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1043, 1360, 1942, 2032, 312, 1153, 1061, 267, 1383, 808, 1320, 2048]
          ![2041, 1460, 432, 528, 16, 704, 1792, 1408, 1536, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1218, 1510, 3, 2, 1660, 480, 1061, 267, 1383, 808, 1320, 2048]
          ![1196, 80, 712, 1368, 304, 224, 1408, 1024, 0, 1536, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048]
          ![1164, 1548, 160, 160, 640, 2016, 704, 1408, 768, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1615, 1743, 2027, 1383, 1310, 323, 546, 643, 2, 3, 1036, 2048]
          ![412, 220, 2024, 1376, 512, 896, 0, 0, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 1499520. -/
def representativePermutationSpinPlan1499520 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 0, 32, 768, 512, 0, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1752, 0, 32, 128, 128, 768, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 2034, 1073, 1652, 1888, 432, 192, 64, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1464, 16, 32, 384, 896, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![425, 1043, 501, 81, 1744, 1888, 1056, 1072, 256, 512, 1024, 2048]
          ![1040, 0, 1504, 1456, 416, 864, 704, 384, 1024, 1024, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1043, 425, 81, 501, 1008, 336, 1056, 1072, 256, 512, 1024, 2048]
          ![1040, 0, 1504, 1456, 176, 96, 704, 256, 256, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![81, 501, 1043, 425, 1216, 64, 1056, 1072, 256, 512, 1024, 2048]
          ![1040, 2, 1504, 1456, 672, 320, 704, 384, 1024, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1698, 122, 794, 1696, 1359, 1423, 1897, 5, 256, 1999, 463, 2048]
          ![901, 1960, 580, 928, 688, 1152, 640, 1792, 1536, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2034, 672, 2042, 154, 192, 1359, 901, 556, 256, 1999, 463, 2048]
          ![5, 40, 448, 1056, 880, 1824, 576, 0, 0, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![672, 2034, 154, 2042, 581, 172, 901, 556, 256, 1999, 463, 2048]
          ![1102, 942, 1164, 1704, 880, 1568, 448, 1152, 1792, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1043, 1045, 889, 1049, 1653, 1915, 102, 1179, 1975, 376, 1912, 2048]
          ![275, 1936, 540, 376, 1504, 576, 512, 384, 1024, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1, 1698, 8, 1896, 1218, 1487, 788, 332, 1975, 972, 1484, 2048]
          ![1599, 530, 564, 184, 1696, 992, 320, 256, 256, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1147, 1975, 1383, 519, 1495, 512, 161, 1059, 1698, 1699, 684, 2048]
          ![446, 1756, 1032, 0, 1856, 1472, 1280, 512, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1900800. -/
def representativePermutationSpinPlan1900800 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 16, 32, 832, 512, 256, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1896, 16, 32, 640, 384, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1702, 1756, 1077, 1092, 1360, 672, 480, 624, 256, 512, 1024, 2048]
          ![1072, 1696, 0, 1752, 736, 416, 704, 256, 768, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1059, 1057, 97, 16, 1965, 1789, 788, 252, 256, 1629, 93, 2048]
          ![483, 1118, 12, 80, 848, 1824, 1408, 1664, 1024, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![761, 1056, 643, 1065, 692, 241, 1000, 788, 256, 1629, 93, 2048]
          ![1734, 764, 1088, 1432, 1504, 1408, 1024, 1536, 256, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![48, 453, 597, 979, 1092, 12, 252, 1000, 256, 1629, 93, 2048]
          ![319, 940, 1084, 2032, 1344, 0, 576, 896, 1792, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![390, 979, 1277, 534, 1941, 1699, 1073, 1152, 1566, 323, 1859, 2048]
          ![662, 1838, 1160, 904, 1568, 1888, 512, 1664, 1792, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1, 1057, 4, 1896, 214, 480, 882, 963, 1566, 323, 1859, 2048]
          ![742, 1098, 1768, 776, 848, 768, 832, 512, 1024, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1885, 1566, 1383, 523, 745, 332, 1154, 1696, 1057, 1056, 47, 2048]
          ![1168, 2032, 736, 1288, 368, 1696, 1216, 1792, 1792, 1024, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1423, 192, 1000, 1156, 1495, 172, 525, 1059, 1698, 1699, 684, 2048]
          ![1892, 1064, 2008, 1712, 544, 320, 384, 1024, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 1943040. -/
def representativePermutationSpinPlan1943040 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 16, 32, 768, 640, 0, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1744, 16, 32, 128, 0, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1045, 2038, 1900, 1156, 1072, 16, 912, 480, 256, 512, 1024, 2048]
          ![1041, 2034, 0, 1896, 240, 128, 896, 640, 256, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![581, 390, 972, 1652, 48, 1040, 1936, 1504, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1456, 272, 800, 128, 128, 768, 1024, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![972, 1652, 581, 390, 1744, 1888, 1936, 1504, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1464, 512, 256, 640, 256, 1280, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![310, 901, 933, 102, 9, 1096, 1648, 779, 2027, 1259, 747, 2048]
          ![535, 1556, 376, 1080, 16, 768, 256, 0, 1024, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1, 1057, 2034, 1073, 1965, 1359, 1156, 1900, 2027, 1516, 1004, 2048]
          ![1163, 136, 1068, 672, 32, 992, 1472, 1152, 1536, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![519, 2027, 1598, 1533, 1127, 1871, 1154, 1696, 1057, 1056, 47, 2048]
          ![1683, 370, 1796, 616, 1008, 448, 1216, 1408, 1792, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![756, 788, 177, 882, 1495, 512, 525, 1059, 1698, 1699, 684, 2048]
          ![1780, 84, 1840, 208, 0, 256, 768, 0, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 1968000. -/
def representativePermutationSpinPlan1968000 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 0, 0, 512, 256, 256, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1888, 0, 0, 960, 640, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1041, 1940, 1362, 1456, 720, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1744, 0, 32, 384, 768, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1509, 534, 292, 1888, 1456, 1648, 1936, 256, 512, 1024, 2048]
          ![0, 2032, 1508, 1752, 544, 288, 576, 256, 1024, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![570, 1362, 402, 672, 2007, 1207, 1092, 1045, 256, 775, 1287, 2048]
          ![1229, 1978, 1704, 1632, 416, 640, 768, 128, 1792, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1898, 1696, 1154, 1090, 864, 2007, 453, 225, 256, 775, 1287, 2048]
          ![284, 1642, 888, 1640, 272, 960, 832, 896, 1536, 0, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1696, 1898, 1090, 1154, 933, 1073, 453, 225, 256, 775, 1287, 2048]
          ![735, 1964, 444, 1640, 256, 736, 256, 384, 1024, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![901, 613, 145, 81, 1706, 8, 1056, 1326, 256, 1854, 318, 2048]
          ![302, 424, 1604, 1152, 16, 768, 832, 768, 1792, 1024, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![192, 81, 1871, 564, 1217, 292, 234, 1117, 1435, 933, 1445, 2048]
          ![1759, 1302, 344, 1080, 848, 1376, 0, 896, 512, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1, 1057, 1652, 783, 177, 469, 1360, 1366, 1435, 852, 1364, 2048]
          ![1375, 738, 144, 1976, 1920, 1472, 384, 1536, 1280, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1743, 1435, 256, 1147, 267, 1259, 1696, 546, 1057, 1056, 47, 2048]
          ![911, 1420, 12, 360, 448, 384, 1088, 1152, 0, 1536, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1466, 1090, 781, 1654, 263, 1342, 1197, 643, 1152, 1153, 142, 2048]
          ![442, 1824, 352, 1536, 1376, 1088, 640, 1280, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 1985280. -/
def representativePermutationSpinPlan1985280 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 16, 0, 576, 256, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1456, 0, 32, 192, 0, 768, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1508, 1896, 1057, 1698, 1936, 480, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1888, 0, 32, 960, 512, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![469, 1081, 355, 177, 1648, 1936, 1040, 1056, 256, 512, 1024, 2048]
          ![1072, 1360, 1508, 0, 608, 448, 448, 896, 1024, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![5, 9, 3, 1, 624, 912, 16, 32, 256, 512, 1024, 2048]
          ![0, 2, 0, 8, 272, 768, 0, 128, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1366, 234, 402, 371, 480, 624, 336, 1696, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1464, 736, 384, 640, 256, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1652, 1, 1057, 1216, 267, 1259, 659, 1706, 256, 1179, 667, 2048]
          ![1892, 1100, 232, 160, 1488, 1920, 1600, 640, 0, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 1088, 4, 1896, 995, 209, 1081, 659, 256, 1179, 667, 2048]
          ![1100, 838, 1692, 232, 272, 1824, 1920, 1024, 256, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1789, 1423, 1639, 267, 556, 852, 16, 1072, 256, 1822, 286, 2048]
          ![1041, 2032, 1072, 840, 1888, 448, 1984, 512, 1024, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1, 1057, 1896, 4, 310, 480, 177, 963, 1885, 323, 1859, 2048]
          ![743, 1096, 1772, 768, 848, 800, 832, 640, 1024, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1566, 1885, 523, 1383, 586, 972, 1154, 1696, 1057, 1056, 47, 2048]
          ![561, 978, 740, 1280, 368, 160, 1216, 1920, 1792, 0, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![192, 1423, 1156, 1000, 376, 556, 525, 1059, 1698, 1699, 684, 2048]
          ![1384, 1188, 376, 16, 544, 448, 384, 512, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 2027520. -/
def representativePermutationSpinPlan2027520 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 8, 16, 0, 576, 256, 256, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 0, 32, 192, 0, 512, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1508, 1896, 1057, 1698, 1936, 480, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1698, 1508, 1896, 0, 32, 960, 512, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![469, 1081, 355, 177, 1648, 1936, 1040, 1056, 256, 512, 1024, 2048]
          ![1073, 1360, 1504, 8, 608, 448, 448, 896, 1280, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1510, 1466, 1090, 1043, 480, 1648, 336, 672, 256, 512, 1024, 2048]
          ![1041, 0, 1508, 1464, 416, 832, 960, 640, 512, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![390, 586, 2034, 963, 1504, 624, 1360, 1696, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1456, 768, 512, 384, 896, 1280, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1220, 209, 241, 1216, 1915, 1691, 1059, 10, 256, 1771, 235, 2048]
          ![452, 158, 1260, 120, 496, 832, 1088, 1152, 1280, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1092, 192, 1089, 97, 480, 1915, 154, 857, 256, 1771, 235, 2048]
          ![1364, 14, 1256, 224, 1584, 960, 1024, 768, 1280, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1073, 2034, 1, 1057, 613, 972, 1000, 1900, 519, 1516, 1004, 2048]
          ![1891, 866, 1704, 1064, 48, 1344, 768, 1920, 0, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1, 1057, 1073, 2034, 738, 1359, 1000, 1900, 519, 1516, 1004, 2048]
          ![1162, 138, 1064, 680, 32, 960, 1472, 1024, 1536, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![2027, 519, 1533, 1598, 1220, 1487, 1154, 1696, 1057, 1056, 47, 2048]
          ![50, 1360, 1792, 608, 1008, 1984, 1216, 1280, 1792, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![788, 756, 882, 177, 376, 128, 525, 1059, 1698, 1699, 684, 2048]
          ![1272, 216, 400, 1648, 0, 384, 768, 1536, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 2386560. -/
def representativePermutationSpinPlan2386560 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 0, 0, 768, 512, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1456, 16, 32, 384, 896, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1698, 1057, 1896, 1508, 1360, 672, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1698, 1508, 1896, 16, 32, 640, 384, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![4, 1, 2, 8, 480, 624, 192, 64, 256, 512, 1024, 2048]
          ![1, 0, 4, 8, 16, 0, 832, 640, 256, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1702, 659, 122, 738, 912, 480, 672, 2032, 256, 512, 1024, 2048]
          ![1073, 1696, 0, 1744, 736, 384, 640, 256, 768, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![794, 546, 310, 1699, 1888, 432, 672, 2032, 256, 512, 1024, 2048]
          ![1, 1696, 1940, 1464, 304, 800, 768, 640, 1280, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1516, 501, 1509, 624, 1207, 2007, 963, 946, 256, 1127, 615, 2048]
          ![1229, 618, 200, 1632, 848, 0, 1024, 1536, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![12, 1648, 1061, 1077, 864, 1207, 610, 1217, 256, 1127, 615, 2048]
          ![285, 954, 1304, 1640, 2032, 576, 768, 256, 1280, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1061, 1077, 12, 1648, 710, 788, 610, 1217, 256, 1127, 615, 2048]
          ![985, 124, 952, 1632, 2032, 416, 1216, 1280, 1536, 1024, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1465, 794, 1456, 972, 102, 1691, 241, 225, 527, 1896, 360, 2048]
          ![698, 528, 756, 56, 320, 1088, 1344, 1920, 0, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![794, 1465, 972, 1456, 664, 274, 241, 225, 527, 1896, 360, 2048]
          ![1853, 752, 528, 32, 1568, 480, 128, 640, 0, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1383, 527, 519, 1147, 1326, 1117, 963, 298, 1465, 1699, 1812, 2048]
          ![1364, 1062, 1000, 1048, 400, 1376, 1984, 1408, 1536, 1024, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1660, 1456, 519, 1888, 512, 2007, 2038, 672, 1698, 1699, 684, 2048]
          ![1640, 1246, 1036, 0, 1856, 2016, 1344, 0, 256, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1654, 1218, 1043, 6, 1495, 512, 161, 1679, 1698, 1699, 684, 2048]
          ![630, 1744, 1536, 208, 1760, 1280, 1664, 256, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 2408640. -/
def representativePermutationSpinPlan2408640 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 16, 32, 704, 256, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1940, 1041, 1362, 1752, 1504, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1752, 0, 0, 896, 640, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![102, 979, 2042, 946, 912, 1504, 1696, 1008, 256, 512, 1024, 2048]
          ![1056, 2034, 1940, 0, 112, 192, 192, 128, 1536, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![2042, 946, 102, 979, 864, 432, 1696, 1008, 256, 512, 1024, 2048]
          ![1056, 2034, 1936, 8, 624, 448, 704, 384, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![2038, 995, 154, 882, 912, 480, 1696, 1008, 256, 512, 1024, 2048]
          ![1040, 2034, 4, 1888, 736, 416, 704, 384, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![92, 376, 312, 720, 267, 1691, 738, 643, 256, 1403, 891, 2048]
          ![1159, 532, 664, 344, 224, 1952, 1728, 1280, 768, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![979, 946, 882, 154, 1117, 263, 610, 838, 527, 1652, 116, 2048]
          ![543, 1900, 592, 496, 544, 1344, 0, 768, 256, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2032, 2035, 672, 298, 1822, 1127, 292, 610, 527, 1652, 116, 2048]
          ![1116, 1062, 592, 544, 960, 0, 1664, 384, 512, 512, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1147, 527, 1239, 1885, 738, 808, 1504, 1045, 2035, 3, 1022, 2048]
          ![1040, 1346, 1940, 1792, 832, 800, 1920, 1920, 256, 1024, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![906, 298, 1239, 172, 1359, 81, 1468, 1900, 2, 3, 1036, 2048]
          ![1006, 1458, 1148, 1240, 0, 128, 0, 128, 256, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![371, 225, 1065, 409, 1310, 1359, 546, 1679, 2, 3, 1036, 2048]
          ![142, 76, 0, 1456, 736, 128, 896, 0, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 2597760. -/
def representativePermutationSpinPlan2597760 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 0, 32, 512, 256, 0, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1508, 1888, 0, 32, 960, 640, 768, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1041, 1940, 1362, 1456, 720, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1744, 0, 0, 384, 768, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1509, 534, 292, 1888, 1456, 1648, 1936, 256, 512, 1024, 2048]
          ![0, 2032, 1504, 1752, 544, 256, 576, 256, 1280, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1754, 1059, 1154, 1654, 720, 1888, 1008, 336, 256, 512, 1024, 2048]
          ![1056, 0, 1648, 1744, 928, 576, 384, 896, 512, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![376, 292, 692, 64, 2007, 263, 1702, 1699, 256, 1127, 615, 2048]
          ![1659, 426, 1000, 984, 528, 288, 256, 384, 1792, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![225, 128, 536, 209, 710, 788, 5, 1702, 256, 1127, 615, 2048]
          ![236, 616, 952, 176, 768, 192, 1728, 1536, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1216, 818, 402, 1224, 1654, 1043, 1699, 5, 256, 1127, 615, 2048]
          ![1471, 206, 1756, 1632, 864, 800, 1664, 1920, 512, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1370, 1224, 775, 2042, 738, 664, 356, 1504, 527, 1896, 360, 2048]
          ![842, 1516, 1912, 904, 1344, 1632, 1472, 512, 1536, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![691, 1040, 995, 1822, 570, 432, 624, 453, 527, 1088, 576, 2048]
          ![901, 456, 464, 1744, 1824, 2016, 640, 1280, 1536, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1615, 527, 256, 1533, 1061, 1756, 480, 806, 1040, 1699, 1725, 2048]
          ![2008, 1066, 76, 944, 400, 320, 1984, 1792, 256, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1277, 1822, 256, 1871, 12, 1366, 1915, 172, 1698, 1699, 684, 2048]
          ![1364, 172, 2000, 1912, 1888, 1024, 1984, 1152, 1792, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2032, 1510, 1466, 269, 1370, 12, 161, 1679, 1698, 1699, 684, 2048]
          ![326, 160, 568, 704, 1728, 1088, 1536, 1024, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 2787840. -/
def representativePermutationSpinPlan2787840 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 16, 0, 704, 384, 512, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1888, 16, 0, 448, 896, 512, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1370, 1363, 371, 1008, 1639, 1207, 241, 692, 256, 1495, 983, 2048]
          ![1098, 74, 988, 2008, 0, 704, 1088, 768, 512, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![710, 1117, 323, 1362, 1089, 3, 241, 692, 256, 1495, 983, 2048]
          ![999, 1442, 980, 1752, 448, 96, 704, 128, 1024, 1024, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1041, 1362, 783, 271, 857, 1900, 312, 972, 1435, 332, 1868, 2048]
          ![962, 12, 104, 1216, 1072, 1152, 1216, 1024, 1536, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1, 1698, 4, 1508, 1090, 1871, 312, 972, 1435, 332, 1868, 2048]
          ![1567, 560, 144, 536, 1696, 1984, 768, 0, 256, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1239, 1435, 2027, 523, 1915, 512, 161, 1059, 1698, 1699, 684, 2048]
          ![926, 1662, 12, 1024, 1472, 640, 1856, 1408, 0, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1326, 949, 48, 1065, 1495, 172, 525, 1679, 1698, 1699, 684, 2048]
          ![642, 1156, 1768, 1904, 416, 1024, 640, 256, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 2830080. -/
def representativePermutationSpinPlan2830080 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 0, 32, 768, 512, 0, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1896, 0, 32, 704, 384, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 1752, 1362, 1940, 1072, 16, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1752, 0, 0, 192, 0, 768, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![113, 664, 738, 1092, 48, 1040, 1152, 1216, 256, 512, 1024, 2048]
          ![1073, 1696, 0, 1744, 480, 928, 960, 512, 256, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![980, 1096, 97, 946, 912, 1504, 64, 1152, 256, 512, 1024, 2048]
          ![1056, 2032, 1936, 0, 880, 704, 640, 256, 1024, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![356, 1160, 177, 466, 1936, 480, 1088, 128, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 8, 880, 736, 640, 384, 256, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![5, 2035, 1363, 1072, 1259, 1915, 1090, 664, 256, 1179, 667, 2048]
          ![1958, 934, 1688, 368, 352, 1792, 640, 1152, 1024, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![9, 1040, 1509, 1897, 1698, 659, 1754, 1090, 256, 1179, 667, 2048]
          ![965, 222, 892, 600, 1968, 1600, 1792, 640, 0, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![12, 1220, 1156, 1756, 1073, 1698, 1915, 912, 256, 1179, 667, 2048]
          ![375, 998, 1692, 1352, 976, 352, 1920, 512, 1024, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![652, 1639, 1000, 432, 1041, 1057, 692, 1660, 1615, 980, 1492, 2048]
          ![1901, 1502, 332, 48, 1200, 864, 1408, 512, 1792, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1898, 570, 889, 154, 782, 1495, 1224, 692, 1615, 980, 1492, 2048]
          ![199, 1220, 60, 1360, 1008, 1248, 1024, 1408, 768, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1, 1698, 2034, 1041, 1942, 332, 64, 1487, 1615, 1871, 335, 2048]
          ![1106, 82, 968, 640, 1392, 0, 1920, 384, 768, 512, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![256, 1615, 1566, 1533, 1915, 172, 161, 1059, 1698, 1699, 684, 2048]
          ![642, 0, 372, 464, 1888, 544, 1984, 512, 1536, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![597, 97, 453, 371, 1495, 512, 525, 1679, 1698, 1699, 684, 2048]
          ![818, 244, 1344, 208, 256, 256, 0, 768, 1024, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 3125760. -/
def representativePermutationSpinPlan3125760 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 0, 32, 512, 256, 256, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 16, 32, 320, 768, 0, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1362, 1041, 1752, 1940, 336, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1362, 1940, 1752, 16, 32, 704, 384, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 1081, 1516, 1160, 2032, 336, 720, 864, 256, 512, 1024, 2048]
          ![1073, 1360, 1504, 8, 624, 448, 640, 256, 768, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1516, 1160, 1370, 1081, 1936, 480, 720, 864, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 8, 368, 960, 960, 512, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![2038, 2035, 963, 672, 1259, 1915, 425, 376, 256, 1179, 667, 2048]
          ![1751, 724, 1688, 0, 1152, 672, 1856, 1024, 768, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![882, 2032, 534, 2034, 841, 371, 209, 425, 256, 1179, 667, 2048]
          ![1749, 1582, 892, 1080, 1088, 1728, 1920, 384, 1792, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![336, 298, 154, 390, 1081, 8, 376, 209, 256, 1179, 667, 2048]
          ![926, 92, 236, 1360, 432, 1152, 0, 1280, 1024, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![48, 409, 841, 597, 10, 1160, 536, 610, 768, 1691, 155, 2048]
          ![831, 1660, 748, 1072, 1936, 32, 576, 768, 1536, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![453, 371, 1059, 1056, 779, 1403, 122, 536, 768, 1691, 155, 2048]
          ![1335, 310, 380, 352, 640, 352, 960, 256, 1536, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![12, 8, 9, 10, 624, 480, 432, 864, 768, 512, 1024, 2048]
          ![0, 0, 0, 8, 512, 256, 512, 384, 768, 512, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![3, 526, 9, 5, 949, 556, 122, 172, 783, 512, 1551, 2048]
          ![172, 556, 992, 352, 512, 288, 576, 896, 256, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![526, 3, 5, 9, 192, 128, 122, 172, 783, 512, 1551, 2048]
          ![0, 128, 64, 192, 0, 0, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 3785280. -/
def representativePermutationSpinPlan3785280 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 0, 32, 768, 512, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1508, 1896, 0, 32, 704, 384, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 1752, 1362, 1940, 1072, 16, 128, 192, 256, 512, 1024, 2048]
          ![1041, 1362, 1940, 1752, 0, 0, 192, 0, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![691, 1706, 214, 610, 1056, 1072, 2032, 1360, 256, 512, 1024, 2048]
          ![1040, 1698, 1648, 8, 352, 960, 448, 768, 1024, 1536, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![214, 610, 691, 1706, 624, 1936, 2032, 1360, 256, 512, 1024, 2048]
          ![1041, 1698, 1652, 8, 96, 192, 128, 0, 768, 1536, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![659, 122, 1702, 738, 1056, 48, 2032, 1360, 256, 512, 1024, 2048]
          ![1072, 1698, 0, 1752, 1008, 640, 896, 640, 1280, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1509, 356, 420, 1504, 1342, 1310, 1218, 10, 256, 1838, 302, 2048]
          ![1327, 792, 1252, 560, 208, 1120, 1664, 1792, 0, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1653, 480, 1652, 692, 32, 1342, 794, 504, 256, 1838, 302, 2048]
          ![1326, 8, 1012, 296, 1808, 1216, 1472, 1408, 1024, 1536, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1652, 692, 1653, 480, 2038, 1756, 794, 504, 256, 1838, 302, 2048]
          ![1327, 1222, 276, 712, 1552, 256, 704, 640, 1280, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![113, 659, 1072, 933, 6, 267, 376, 1464, 1383, 841, 1353, 2048]
          ![1960, 186, 1568, 784, 160, 416, 256, 768, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![177, 32, 1075, 469, 1629, 1179, 1216, 376, 1383, 841, 1353, 2048]
          ![953, 1890, 1320, 1096, 1296, 1440, 1728, 768, 1280, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1366, 1756, 1504, 6, 161, 949, 1217, 610, 1383, 1127, 615, 2048]
          ![12, 2024, 1676, 184, 1568, 224, 768, 768, 512, 512, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1366, 4, 1504, 6, 1453, 738, 154, 979, 1072, 1153, 1215, 2048]
          ![1748, 1324, 408, 1080, 1104, 480, 128, 1536, 1024, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1510, 469, 1504, 182, 1197, 643, 298, 946, 1152, 1153, 142, 2048]
          ![516, 380, 1400, 1072, 1984, 704, 0, 1280, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 3824640. -/
def representativePermutationSpinPlan3824640 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 0, 0, 512, 256, 0, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 16, 0, 320, 768, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1057, 1508, 1896, 1698, 32, 1072, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1888, 16, 0, 128, 128, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1065, 1948, 2042, 1096, 1040, 32, 864, 432, 256, 512, 1024, 2048]
          ![1057, 2034, 1940, 0, 96, 192, 448, 896, 0, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1948, 1065, 1096, 2042, 1648, 912, 864, 432, 256, 512, 1024, 2048]
          ![1057, 2034, 1940, 0, 368, 960, 896, 640, 512, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1096, 2042, 1948, 1065, 1216, 64, 864, 432, 256, 512, 1024, 2048]
          ![1057, 2034, 1936, 0, 880, 736, 128, 0, 0, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1652, 1653, 597, 480, 1359, 1423, 745, 906, 256, 1999, 463, 2048]
          ![1893, 456, 868, 8, 48, 1504, 1024, 896, 1280, 1536, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![912, 972, 756, 284, 10, 1059, 745, 906, 256, 1999, 463, 2048]
          ![206, 1166, 668, 1936, 528, 1728, 1280, 1280, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1508, 1041, 4, 1073, 1065, 10, 1359, 1423, 256, 1999, 463, 2048]
          ![229, 584, 1252, 896, 496, 1600, 1088, 1024, 0, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1077, 1073, 1854, 32, 504, 864, 1941, 788, 2027, 292, 1828, 2048]
          ![879, 1590, 1932, 1320, 544, 1920, 1920, 384, 1280, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1081, 857, 745, 659, 1059, 1838, 1941, 788, 2027, 292, 1828, 2048]
          ![1892, 140, 344, 1160, 1584, 1632, 1344, 640, 1792, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1081, 1073, 745, 659, 64, 1156, 92, 409, 1089, 3, 76, 2048]
          ![1536, 966, 1748, 1288, 1568, 704, 1280, 128, 256, 1024, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![122, 664, 745, 1744, 1679, 161, 720, 1468, 2, 3, 1036, 2048]
          ![108, 1536, 0, 1744, 224, 896, 128, 256, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 5197440. -/
def representativePermutationSpinPlan5197440 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 0, 16, 32, 576, 384, 256, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 0, 32, 256, 896, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 16, 0, 960, 640, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![597, 761, 1059, 161, 624, 1936, 1040, 32, 256, 512, 1024, 2048]
          ![1056, 2, 1652, 1752, 944, 608, 640, 384, 1280, 1024, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![901, 713, 323, 1041, 1648, 912, 16, 1056, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 272, 800, 128, 0, 1536, 1024, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1043, 81, 501, 425, 336, 672, 16, 1056, 256, 512, 1024, 2048]
          ![1040, 2, 1508, 1456, 176, 64, 704, 384, 0, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1702, 12, 1468, 1504, 269, 1117, 761, 1057, 256, 1277, 765, 2048]
          ![1651, 92, 200, 1216, 800, 1056, 960, 1280, 256, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![310, 480, 252, 332, 1360, 269, 209, 376, 256, 1277, 765, 2048]
          ![643, 94, 56, 1072, 176, 1120, 192, 1280, 1024, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![480, 310, 332, 252, 1153, 1160, 209, 376, 256, 1277, 765, 2048]
          ![1710, 94, 236, 1512, 1408, 1440, 1408, 256, 1280, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1, 1073, 1896, 1752, 390, 2042, 128, 1487, 256, 1935, 399, 2048]
          ![1208, 836, 708, 184, 1456, 1408, 384, 1536, 768, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1691, 980, 252, 332, 586, 979, 241, 1217, 2027, 356, 1892, 2048]
          ![535, 1532, 376, 1216, 1472, 832, 448, 1664, 512, 0, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1854, 1073, 857, 745, 2042, 390, 852, 292, 526, 1153, 641, 2048]
          ![1343, 1532, 532, 296, 576, 1024, 384, 384, 1024, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![432, 1383, 857, 1127, 946, 534, 402, 692, 1152, 1153, 142, 2048]
          ![14, 1324, 1304, 0, 1088, 1216, 256, 1536, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 5786880. -/
def representativePermutationSpinPlan5786880 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 0, 32, 512, 384, 256, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1754, 761, 172, 600, 1008, 336, 720, 1888, 256, 512, 1024, 2048]
          ![1056, 2, 1652, 1744, 928, 576, 448, 768, 768, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![172, 600, 1754, 761, 1936, 1504, 720, 1888, 256, 512, 1024, 2048]
          ![1056, 0, 1648, 1744, 160, 64, 192, 128, 512, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![310, 691, 643, 1696, 1915, 1259, 1897, 936, 256, 779, 1291, 2048]
          ![6, 1030, 1692, 328, 400, 672, 64, 0, 0, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![546, 1008, 214, 1698, 393, 1075, 1217, 1897, 256, 779, 1291, 2048]
          ![1364, 1596, 1912, 1056, 288, 704, 256, 768, 256, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![336, 1706, 794, 838, 761, 1752, 936, 1217, 256, 779, 1291, 2048]
          ![927, 94, 1256, 1368, 64, 768, 512, 640, 512, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1072, 857, 393, 469, 906, 600, 1224, 818, 768, 267, 1803, 2048]
          ![1854, 638, 1768, 56, 912, 32, 384, 896, 1536, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![581, 1075, 355, 32, 1179, 1771, 2042, 1224, 768, 267, 1803, 2048]
          ![2022, 996, 1400, 1064, 272, 352, 512, 256, 1280, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![332, 1752, 713, 906, 1648, 1504, 1456, 1888, 768, 512, 1024, 2048]
          ![1041, 1362, 1940, 1744, 512, 256, 640, 256, 1280, 512, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![323, 1566, 713, 901, 1077, 1900, 2042, 1516, 783, 512, 1551, 2048]
          ![509, 574, 308, 760, 528, 288, 128, 512, 1792, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1363, 1153, 1056, 2035, 857, 1077, 214, 122, 783, 512, 1551, 2048]
          ![1784, 1012, 400, 528, 416, 960, 384, 0, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 6125760. -/
def representativePermutationSpinPlan6125760 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 16, 32, 576, 256, 0, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 8, 0, 32, 256, 768, 256, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1362, 1041, 1752, 1940, 336, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 0, 32, 640, 384, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 1081, 1516, 1160, 2032, 336, 720, 864, 256, 512, 1024, 2048]
          ![1072, 1362, 1508, 0, 608, 448, 704, 256, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![806, 1653, 564, 284, 1696, 2032, 1936, 1504, 256, 512, 1024, 2048]
          ![0, 1360, 1652, 1888, 816, 544, 320, 768, 1280, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![546, 1160, 1000, 192, 1117, 1789, 1468, 1077, 256, 781, 1293, 2048]
          ![1895, 1966, 1216, 496, 768, 704, 0, 768, 1024, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1698, 1216, 1752, 1464, 672, 1117, 613, 889, 256, 781, 1293, 2048]
          ![310, 1964, 656, 928, 624, 0, 768, 128, 1536, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1, 4, 271, 8, 980, 332, 613, 889, 256, 781, 1293, 2048]
          ![333, 2, 224, 176, 784, 288, 832, 384, 0, 0, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![263, 8, 775, 12, 972, 376, 355, 857, 526, 3, 1539, 2048]
          ![377, 972, 852, 984, 0, 768, 0, 512, 256, 512, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![779, 256, 775, 512, 864, 720, 963, 241, 2, 3, 1036, 2048]
          ![735, 878, 8, 0, 528, 256, 576, 256, 256, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1936, 949, 980, 102, 432, 864, 912, 1516, 2, 3, 1036, 2048]
          ![1424, 1168, 1936, 0, 608, 704, 384, 256, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 6673920. -/
def representativePermutationSpinPlan6673920 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 16, 0, 512, 384, 256, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1752, 1940, 1362, 1041, 720, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1744, 16, 0, 384, 768, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![936, 852, 1218, 241, 1744, 864, 1088, 1152, 256, 512, 1024, 2048]
          ![1073, 2, 1936, 1896, 672, 320, 960, 512, 1024, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![209, 692, 1224, 610, 1056, 1072, 192, 1088, 256, 512, 1024, 2048]
          ![1041, 1698, 1648, 0, 864, 736, 448, 896, 0, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1089, 564, 808, 274, 32, 48, 1216, 64, 256, 512, 1024, 2048]
          ![0, 1360, 1652, 1896, 48, 0, 64, 128, 512, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![393, 794, 234, 720, 270, 1326, 818, 852, 256, 1822, 286, 2048]
          ![303, 1160, 1360, 128, 1056, 1536, 512, 640, 1024, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![972, 864, 1465, 1468, 2, 1898, 102, 818, 256, 1822, 286, 2048]
          ![1310, 596, 20, 520, 208, 928, 128, 512, 0, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![271, 263, 267, 270, 613, 889, 672, 336, 256, 781, 1293, 2048]
          ![337, 2, 1012, 672, 0, 32, 576, 384, 256, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![794, 234, 1468, 1465, 209, 32, 2042, 2034, 1615, 1090, 578, 2048]
          ![1558, 258, 16, 464, 976, 928, 192, 384, 1280, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![775, 263, 12, 9, 889, 613, 586, 946, 527, 2, 1538, 2048]
          ![581, 286, 500, 464, 16, 544, 0, 384, 256, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![525, 527, 526, 523, 113, 581, 864, 432, 263, 512, 1543, 2048]
          ![865, 2, 724, 8, 272, 800, 768, 640, 512, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![5, 9, 526, 3, 355, 857, 122, 172, 783, 512, 1551, 2048]
          ![122, 500, 568, 944, 256, 768, 256, 512, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 10665600. -/
def representativePermutationSpinPlan10665600 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1456, 16, 0, 640, 256, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1896, 16, 0, 384, 768, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 4, 8, 2, 32, 48, 192, 64, 256, 512, 1024, 2048]
          ![0, 2, 0, 0, 16, 32, 0, 128, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 284, 570, 808, 16, 32, 864, 1456, 256, 512, 1024, 2048]
          ![1, 1360, 1648, 1888, 800, 544, 64, 0, 512, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![393, 972, 586, 1464, 1040, 1056, 1888, 432, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1456, 784, 512, 192, 128, 1792, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![355, 182, 466, 1370, 48, 1040, 1696, 2032, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 0, 352, 992, 384, 896, 0, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1057, 1464, 8, 1152, 1342, 270, 1898, 1654, 256, 1822, 286, 2048]
          ![318, 372, 1088, 2032, 832, 1760, 320, 0, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1216, 1073, 4, 122, 600, 284, 1898, 256, 1822, 286, 2048]
          ![303, 2, 1740, 816, 1440, 128, 1536, 0, 1792, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![453, 979, 371, 597, 546, 122, 270, 1072, 256, 1822, 286, 2048]
          ![319, 1222, 196, 1360, 816, 1824, 64, 896, 1280, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1077, 267, 1366, 1648, 610, 738, 2035, 1509, 525, 1043, 531, 2048]
          ![943, 310, 136, 1584, 432, 736, 640, 1024, 1792, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1900, 12, 1220, 1468, 783, 1403, 534, 2035, 525, 1043, 531, 2048]
          ![143, 1158, 0, 536, 736, 1088, 1024, 896, 1792, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1698, 122, 794, 610, 889, 613, 672, 1789, 525, 781, 1293, 2048]
          ![310, 1964, 656, 928, 608, 32, 768, 128, 1792, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![256, 525, 1743, 1975, 270, 1653, 274, 808, 122, 1752, 1141, 2048]
          ![1793, 906, 368, 456, 1360, 160, 384, 128, 0, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1117, 1360, 906, 1362, 1147, 526, 1871, 1127, 643, 1702, 1397, 3069]
          ![1515, 372, 736, 1912, 272, 1152, 128, 1280, 1536, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![564, 1090, 738, 1092, 1363, 1885, 512, 1639, 161, 16, 296, 2487]
          ![319, 1788, 764, 208, 832, 704, 256, 256, 1280, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![782, 781, 1838, 1854, 1615, 274, 1915, 284, 1160, 788, 796, 3087]
          ![795, 1818, 988, 1696, 1200, 544, 64, 0, 1280, 1024, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![782, 1822, 1838, 1854, 252, 154, 64, 128, 1280, 768, 1807, 3087]
          ![14, 1036, 1032, 1024, 96, 128, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 10665792. -/
def representativePermutationSpinPlan10665792 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 0, 32, 768, 640, 0, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1744, 0, 32, 128, 0, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1045, 2038, 1900, 1156, 1072, 16, 912, 480, 256, 512, 1024, 2048]
          ![1041, 2032, 4, 1896, 224, 128, 896, 640, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![425, 1466, 504, 92, 1056, 1072, 1744, 1888, 256, 512, 1024, 2048]
          ![1040, 0, 1508, 1464, 432, 864, 640, 384, 1024, 1536, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![504, 92, 425, 1466, 64, 1152, 1744, 1888, 256, 512, 1024, 2048]
          ![1041, 0, 1508, 1464, 672, 320, 960, 640, 0, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1217, 1363, 3, 1040, 1359, 271, 2042, 1660, 256, 1935, 399, 2048]
          ![866, 1888, 1080, 368, 400, 352, 1600, 1280, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1509, 1056, 1089, 5, 122, 691, 390, 2042, 256, 1935, 399, 2048]
          ![1193, 836, 1572, 8, 1600, 1536, 128, 1280, 1792, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![292, 936, 376, 692, 713, 122, 271, 1088, 256, 1935, 399, 2048]
          ![243, 1456, 44, 1064, 768, 32, 1984, 1024, 1280, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1092, 267, 1468, 1648, 761, 745, 1896, 1508, 519, 1160, 648, 2048]
          ![1221, 1604, 24, 328, 1712, 704, 704, 768, 1792, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2038, 6, 1061, 1366, 782, 1403, 652, 1896, 519, 1160, 648, 2048]
          ![1667, 642, 8, 1048, 2000, 1088, 1152, 1536, 1792, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1753, 122, 906, 761, 882, 756, 720, 1639, 519, 775, 1287, 2048]
          ![2010, 984, 664, 2000, 912, 896, 192, 640, 1792, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![256, 519, 1582, 1885, 271, 1652, 393, 963, 122, 1699, 1140, 2048]
          ![1098, 298, 368, 792, 352, 384, 64, 1408, 0, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1207, 1456, 794, 1465, 1147, 527, 1854, 1277, 536, 1756, 1396, 2919]
          ![263, 1906, 744, 368, 1520, 0, 1024, 1280, 1536, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![581, 1081, 745, 1077, 1464, 1975, 512, 1789, 209, 128, 451, 2397]
          ![1518, 172, 620, 1632, 128, 320, 512, 384, 1280, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![783, 775, 1999, 1871, 1598, 393, 1915, 390, 1043, 901, 902, 3086]
          ![375, 1756, 932, 1928, 144, 32, 704, 1536, 1280, 1024, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![783, 1935, 1999, 1871, 102, 154, 48, 16, 1280, 768, 1806, 3086]
          ![1038, 1036, 1032, 1024, 64, 128, 128, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 10666560. -/
def representativePermutationSpinPlan10666560 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 16, 32, 704, 256, 512, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1888, 16, 32, 448, 768, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 4, 8, 2, 32, 48, 192, 64, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 16, 0, 64, 128, 0, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1652, 1073, 1464, 1008, 1360, 128, 192, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1464, 16, 0, 640, 256, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2035, 1509, 1753, 1217, 1696, 1008, 48, 16, 256, 512, 1024, 2048]
          ![1, 2034, 1504, 1744, 560, 256, 64, 128, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 5, 3, 9, 192, 64, 32, 48, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 16, 0, 0, 0, 256, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![738, 458, 1706, 1696, 271, 1487, 713, 501, 256, 1935, 399, 2048]
          ![565, 1626, 2036, 592, 464, 384, 512, 640, 1792, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![946, 672, 586, 298, 1216, 271, 1653, 1660, 256, 1935, 399, 2048]
          ![1461, 1498, 112, 464, 16, 512, 320, 256, 0, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![10, 3, 1466, 1754, 1896, 4, 806, 564, 2027, 356, 1892, 2048]
          ![1595, 1886, 708, 568, 2016, 1792, 704, 256, 256, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1652, 1653, 1915, 613, 12, 1888, 1090, 1360, 2027, 356, 1892, 2048]
          ![14, 658, 396, 1176, 1920, 1344, 1344, 256, 1024, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1464, 393, 794, 504, 1900, 12, 979, 1789, 2027, 356, 1892, 2048]
          ![300, 1328, 116, 1704, 1136, 1024, 1856, 640, 256, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1679, 2027, 1615, 1197, 270, 9, 225, 936, 393, 1073, 1414, 2048]
          ![1095, 860, 408, 1088, 768, 320, 384, 896, 1792, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1326, 453, 16, 1057, 519, 526, 64, 1000, 234, 425, 777, 3069]
          ![440, 1794, 1500, 8, 192, 512, 512, 0, 768, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1224, 292, 376, 209, 1056, 1582, 1423, 1639, 1629, 906, 1575, 2733]
          ![1552, 92, 564, 104, 1312, 832, 1792, 512, 768, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1153, 356, 466, 600, 1743, 225, 263, 1888, 1403, 1179, 751, 3087]
          ![285, 590, 924, 440, 1872, 1248, 768, 1664, 1536, 0, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1153, 1156, 466, 600, 252, 154, 1871, 128, 1280, 768, 1807, 3087]
          ![1792, 1104, 1024, 1232, 1728, 896, 128, 1792, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 10667712. -/
def representativePermutationSpinPlan10667712 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1456, 0, 0, 640, 384, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1896, 0, 0, 384, 896, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![154, 2038, 995, 882, 1456, 1744, 1360, 1696, 256, 512, 1024, 2048]
          ![1041, 2032, 0, 1888, 224, 160, 192, 0, 1536, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![10, 6, 3, 2, 432, 720, 336, 672, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 272, 800, 768, 640, 768, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![3, 2, 10, 6, 16, 32, 336, 672, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 512, 256, 0, 0, 256, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![841, 284, 1900, 1888, 270, 1310, 534, 946, 256, 1854, 318, 2048]
          ![286, 162, 476, 1496, 656, 352, 0, 256, 1280, 1024, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1789, 390, 586, 2034, 48, 1056, 808, 652, 256, 1854, 318, 2048]
          ![1073, 2034, 1604, 400, 96, 1728, 192, 1152, 512, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![356, 192, 312, 1152, 371, 1061, 284, 1639, 1197, 659, 1171, 2048]
          ![879, 6, 1888, 336, 1296, 320, 896, 128, 1024, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1153, 1160, 1156, 145, 298, 864, 284, 1639, 1197, 659, 1171, 2048]
          ![320, 92, 732, 640, 720, 320, 1024, 0, 1024, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1598, 1197, 1566, 523, 271, 1464, 1403, 1277, 1160, 9, 134, 2048]
          ![184, 1622, 1528, 1696, 1248, 1728, 128, 128, 1024, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1915, 214, 1660, 1653, 1975, 527, 1854, 963, 1154, 466, 1720, 2919]
          ![147, 528, 736, 1416, 1520, 960, 640, 128, 0, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1719, 1453, 1935, 1629, 1652, 1147, 1342, 1789, 1059, 1510, 451, 3083]
          ![284, 1100, 1160, 952, 1296, 224, 1088, 1024, 0, 0, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1073, 659, 1075, 469, 256, 1403, 1207, 586, 225, 949, 1908, 3086]
          ![1657, 1794, 1764, 304, 1712, 288, 1984, 896, 0, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1073, 745, 1075, 469, 102, 154, 48, 1822, 1280, 768, 1806, 3086]
          ![816, 1024, 1248, 1232, 1952, 1856, 1280, 1536, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 10668768. -/
def representativePermutationSpinPlan10668768 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 16, 0, 512, 384, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1456, 0, 32, 128, 128, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1362, 1041, 1940, 1888, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 16, 0, 384, 896, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1698, 1896, 1057, 1648, 1936, 128, 192, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1896, 0, 0, 960, 512, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 298, 1753, 536, 480, 1648, 1456, 720, 256, 512, 1024, 2048]
          ![1, 2032, 1508, 1752, 544, 256, 512, 384, 1024, 1024, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![972, 586, 393, 1464, 1504, 624, 432, 1744, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 528, 256, 704, 384, 1280, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1653, 1363, 1089, 1897, 1936, 1504, 48, 16, 256, 512, 1024, 2048]
          ![0, 1362, 1652, 1896, 288, 768, 0, 0, 512, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1940, 1464, 1896, 1088, 1915, 1259, 761, 979, 256, 779, 1291, 2048]
          ![311, 932, 1688, 664, 32, 960, 512, 512, 1536, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![852, 64, 1224, 536, 912, 1915, 1699, 458, 256, 779, 1291, 2048]
          ![1095, 1750, 1692, 1000, 336, 800, 320, 384, 1536, 1024, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1224, 536, 852, 64, 81, 274, 1699, 458, 256, 779, 1291, 2048]
          ![292, 190, 1688, 1928, 336, 288, 576, 128, 1280, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![788, 64, 1935, 600, 1056, 409, 1508, 1896, 519, 12, 1548, 2048]
          ![1733, 1092, 700, 1040, 848, 768, 576, 512, 1536, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1363, 1008, 906, 1629, 1936, 1468, 1652, 271, 519, 1065, 553, 2048]
          ![146, 546, 856, 1072, 1872, 192, 1600, 640, 1536, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1582, 519, 256, 1239, 1639, 720, 613, 901, 1008, 1699, 2046, 2048]
          ![206, 796, 1304, 8, 704, 1952, 1408, 1024, 256, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1915, 1660, 214, 1653, 1975, 1383, 48, 949, 1360, 466, 464, 3087]
          ![321, 48, 736, 216, 1520, 1856, 704, 512, 0, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![425, 1049, 323, 145, 284, 1147, 1326, 1691, 1075, 1090, 1707, 2775]
          ![362, 742, 1076, 960, 1024, 0, 704, 640, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![841, 1065, 1059, 97, 1566, 613, 1207, 556, 241, 963, 1794, 3086]
          ![1657, 300, 1076, 928, 208, 160, 1472, 1664, 0, 512, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![841, 1061, 1059, 97, 102, 1940, 1854, 1822, 1280, 768, 1806, 3086]
          ![800, 512, 256, 96, 64, 192, 1536, 768, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 10773794. -/
def representativePermutationSpinPlan10773794 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 16, 0, 832, 640, 256, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1888, 16, 0, 640, 256, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1702, 1756, 1077, 1092, 1360, 672, 480, 624, 256, 512, 1024, 2048]
          ![1073, 1698, 0, 1744, 736, 384, 704, 384, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![691, 1049, 209, 613, 2032, 1360, 1056, 1072, 256, 512, 1024, 2048]
          ![1041, 1696, 1648, 0, 368, 960, 384, 896, 1024, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![3, 9, 1, 5, 1008, 336, 32, 48, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 512, 288, 0, 0, 256, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![466, 756, 1156, 1152, 269, 1789, 501, 713, 256, 1453, 941, 2048]
          ![570, 764, 836, 1216, 752, 160, 512, 640, 1280, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1160, 192, 1154, 1000, 933, 1940, 828, 501, 256, 1453, 941, 2048]
          ![1891, 1966, 108, 600, 1392, 1216, 1728, 1920, 512, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![64, 161, 177, 882, 5, 1897, 713, 828, 256, 1453, 941, 2048]
          ![1102, 94, 2040, 672, 512, 960, 1728, 1920, 1536, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![624, 901, 933, 102, 1089, 9, 761, 536, 768, 1965, 429, 2048]
          ![1662, 606, 380, 2040, 0, 1856, 1664, 1024, 256, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1838, 161, 16, 979, 1897, 5, 332, 2007, 1743, 610, 1122, 2048]
          ![1101, 90, 288, 792, 1392, 1312, 1792, 0, 256, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![889, 613, 995, 32, 1453, 1702, 1752, 1744, 1743, 1217, 705, 2048]
          ![1273, 1914, 1588, 1656, 16, 0, 832, 128, 512, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![526, 1743, 1598, 1533, 263, 267, 2, 781, 613, 284, 258, 2048]
          ![284, 664, 2032, 1224, 208, 992, 320, 640, 1024, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![8, 1216, 1652, 1896, 523, 768, 3, 782, 501, 48, 780, 2775]
          ![545, 602, 1136, 888, 416, 768, 0, 512, 1536, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![6, 1218, 1043, 1059, 271, 527, 9, 775, 182, 420, 772, 3069]
          ![529, 1054, 172, 96, 224, 448, 64, 768, 1280, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![270, 1217, 1509, 1089, 525, 2, 12, 779, 466, 234, 770, 2919]
          ![798, 984, 1356, 1504, 512, 128, 64, 128, 768, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![270, 1699, 1509, 1089, 1719, 1495, 355, 1075, 1031, 519, 352, 2919]
          ![1700, 1380, 240, 1792, 480, 1344, 1536, 1024, 1536, 0, 0, 0])]

/-- Intermediate spin models for source permutation 11552640. -/
def representativePermutationSpinPlan11552640 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1456, 16, 0, 704, 256, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![154, 889, 1900, 1000, 1008, 1360, 1744, 864, 256, 512, 1024, 2048]
          ![1041, 2034, 4, 1888, 240, 160, 192, 128, 1536, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![252, 936, 1898, 857, 912, 1504, 1744, 864, 256, 512, 1024, 2048]
          ![1073, 0, 1936, 1888, 176, 64, 192, 128, 1536, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![214, 1699, 659, 1696, 1691, 267, 713, 600, 256, 1771, 235, 2048]
          ![503, 1526, 668, 1368, 896, 96, 896, 896, 512, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![390, 672, 979, 995, 1936, 1691, 808, 113, 256, 1771, 235, 2048]
          ![1159, 134, 664, 1064, 1776, 1952, 1920, 896, 1792, 1024, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![979, 995, 390, 672, 10, 1218, 808, 113, 256, 1771, 235, 2048]
          ![309, 990, 668, 144, 16, 1504, 512, 0, 768, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![933, 252, 480, 710, 1754, 269, 81, 97, 527, 1508, 996, 2048]
          ![284, 400, 1632, 944, 1504, 1216, 512, 512, 512, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![852, 556, 1691, 1948, 336, 214, 81, 97, 527, 1508, 996, 2048]
          ![937, 1452, 284, 8, 1856, 960, 1280, 896, 1024, 1536, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![263, 768, 1691, 1487, 122, 643, 808, 564, 92, 1508, 1107, 2048]
          ![1537, 850, 652, 1368, 736, 352, 704, 896, 768, 1024, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![768, 263, 1487, 1691, 782, 1363, 808, 564, 92, 1508, 1107, 2048]
          ![1537, 848, 972, 648, 144, 2016, 896, 128, 1024, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1127, 1888, 652, 1896, 1117, 270, 1615, 1147, 393, 1466, 1875, 2775]
          ![2045, 504, 1620, 848, 1152, 1920, 128, 1792, 1536, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![274, 1096, 504, 1090, 1897, 1639, 256, 1403, 177, 32, 820, 2971]
          ![799, 478, 232, 1488, 448, 928, 768, 768, 0, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![526, 519, 1598, 1566, 1359, 808, 1629, 806, 1156, 546, 550, 3087]
          ![557, 742, 1464, 1576, 304, 1408, 64, 0, 256, 1536, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![526, 1582, 1598, 1566, 214, 172, 64, 128, 1792, 512, 1551, 3087]
          ![14, 1036, 1032, 1024, 160, 192, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 11706825. -/
def representativePermutationSpinPlan11706825 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 16, 0, 512, 384, 0, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 0, 0, 320, 896, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1057, 1508, 1896, 1698, 32, 1072, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1888, 0, 0, 128, 0, 512, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1362, 1940, 1041, 1752, 2032, 336, 128, 192, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 0, 32, 640, 256, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![946, 980, 97, 1096, 1008, 1360, 1152, 1216, 256, 512, 1024, 2048]
          ![1056, 2034, 1936, 8, 864, 704, 960, 512, 256, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![664, 1092, 738, 113, 720, 1888, 64, 1152, 256, 512, 1024, 2048]
          ![1072, 1696, 0, 1752, 496, 928, 704, 384, 1280, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![234, 323, 355, 1008, 2007, 263, 161, 788, 256, 1127, 615, 2048]
          ![1514, 490, 972, 976, 1392, 1984, 128, 1536, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1366, 1360, 906, 182, 1217, 1699, 949, 161, 256, 1127, 615, 2048]
          ![12, 2024, 1672, 184, 1568, 224, 768, 896, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1468, 1464, 504, 556, 610, 1217, 263, 1744, 256, 1127, 615, 2048]
          ![426, 1656, 56, 984, 1936, 1088, 192, 1792, 1024, 512, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1423, 1259, 1359, 1691, 818, 1218, 1456, 775, 1239, 432, 1968, 2048]
          ![1598, 142, 2040, 696, 160, 1312, 768, 1152, 1792, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![2034, 1073, 1940, 1088, 1000, 1898, 1049, 9, 1239, 536, 1048, 2048]
          ![341, 594, 1272, 352, 160, 1312, 320, 1536, 1536, 512, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![980, 1435, 1940, 102, 1639, 1897, 1456, 10, 241, 536, 550, 2048]
          ![1300, 1862, 1772, 264, 896, 480, 128, 384, 768, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1435, 980, 102, 1940, 806, 1403, 1456, 10, 241, 536, 550, 2048]
          ![1310, 1974, 1772, 1096, 1072, 992, 128, 768, 256, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![234, 504, 376, 864, 1179, 480, 519, 525, 659, 16, 1981, 3328]
          ![935, 1092, 1000, 1880, 128, 800, 64, 640, 1280, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![775, 1096, 1081, 1065, 972, 556, 1885, 1360, 838, 691, 1879, 3087]
          ![719, 1116, 136, 216, 592, 928, 192, 384, 1280, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1147, 1615, 1197, 1566, 1948, 1456, 1629, 781, 1504, 652, 1104, 2775]
          ![940, 242, 452, 312, 1280, 256, 1344, 384, 1792, 512, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1147, 526, 1197, 1566, 1898, 269, 534, 2042, 349, 710, 17, 2775]
          ![1004, 1372, 1016, 1696, 1984, 896, 1024, 768, 1536, 0, 0, 0])]

/-- Intermediate spin models for source permutation 11996160. -/
def representativePermutationSpinPlan11996160 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 0, 0, 832, 512, 256, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1744, 0, 0, 192, 128, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 2034, 1073, 1652, 1888, 432, 192, 64, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1456, 16, 0, 448, 896, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![4, 2, 8, 1, 624, 912, 128, 192, 256, 512, 1024, 2048]
          ![1, 0, 4, 8, 0, 32, 768, 640, 0, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![420, 1090, 504, 81, 1648, 1936, 1152, 1216, 256, 512, 1024, 2048]
          ![1040, 2, 1504, 1456, 672, 320, 448, 896, 1280, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![172, 1753, 713, 864, 1259, 1691, 1057, 2034, 256, 779, 1291, 2048]
          ![412, 1044, 1916, 1432, 256, 224, 384, 128, 1280, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1660, 1888, 1081, 1065, 624, 1259, 274, 323, 256, 779, 1291, 2048]
          ![892, 758, 1912, 1912, 592, 0, 512, 256, 1792, 512, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![16, 1065, 1838, 841, 1089, 1, 64, 209, 1147, 1648, 112, 2048]
          ![639, 796, 1912, 0, 800, 608, 640, 128, 256, 1024, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1217, 1224, 292, 402, 1073, 113, 48, 161, 1147, 1648, 112, 2048]
          ![363, 304, 404, 24, 736, 1536, 320, 1792, 1280, 512, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1217, 818, 292, 402, 1156, 1935, 1915, 1342, 901, 1041, 1930, 2048]
          ![926, 992, 1872, 712, 272, 1664, 0, 1536, 1536, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1423, 1789, 1359, 1207, 782, 5, 241, 692, 901, 1041, 1930, 2048]
          ![1099, 940, 1096, 608, 832, 320, 896, 640, 512, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1854, 963, 32, 1073, 267, 270, 64, 756, 252, 949, 517, 2775]
          ![916, 2022, 4, 1544, 256, 448, 256, 0, 1792, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1220, 818, 852, 225, 1072, 1342, 1935, 1403, 1383, 652, 1339, 2487]
          ![1312, 282, 124, 96, 608, 1376, 1536, 256, 768, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1153, 882, 1000, 356, 1487, 241, 779, 1648, 1885, 1197, 511, 3087]
          ![807, 686, 924, 328, 1232, 640, 512, 1408, 1536, 1024, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1153, 1154, 1000, 356, 214, 172, 1615, 128, 1792, 512, 1551, 3087]
          ![1536, 1024, 1248, 1120, 640, 1856, 128, 1536, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 12883200. -/
def representativePermutationSpinPlan12883200 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 16, 0, 512, 256, 256, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 0, 32, 128, 0, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![469, 182, 1516, 356, 48, 1040, 1936, 480, 256, 512, 1024, 2048]
          ![1073, 1360, 1504, 0, 608, 448, 448, 896, 1280, 1024, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![901, 710, 332, 1940, 1072, 16, 912, 1504, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1752, 256, 768, 128, 0, 1536, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1897, 1000, 1896, 432, 1310, 1326, 420, 534, 256, 1854, 318, 2048]
          ![1343, 4, 308, 672, 656, 1152, 128, 1408, 256, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![9, 1456, 1224, 1096, 48, 1310, 310, 1698, 256, 1854, 318, 2048]
          ![1342, 806, 532, 1408, 720, 832, 448, 1664, 1024, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1370, 1516, 263, 1160, 172, 692, 310, 1698, 256, 1854, 318, 2048]
          ![1073, 2020, 92, 1936, 1152, 896, 384, 0, 0, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1057, 949, 1326, 161, 564, 1653, 838, 1008, 523, 1077, 565, 2048]
          ![238, 1040, 292, 1576, 1296, 1184, 1728, 1920, 0, 0, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![949, 1057, 161, 1326, 889, 432, 838, 1008, 523, 1077, 565, 2048]
          ![89, 982, 1620, 1496, 1104, 1504, 192, 1408, 1792, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1598, 523, 768, 1679, 1363, 1753, 420, 81, 1057, 1940, 1978, 2048]
          ![1460, 1282, 896, 184, 1712, 1376, 1344, 1408, 0, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1423, 1326, 768, 1342, 782, 1040, 1096, 664, 1936, 1940, 927, 2048]
          ![15, 94, 584, 1856, 192, 928, 768, 1792, 1536, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![775, 1065, 1948, 8, 1310, 270, 192, 600, 1504, 1366, 1552, 2733]
          ![305, 1536, 1312, 944, 160, 704, 1280, 1024, 1280, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![81, 97, 1092, 274, 9, 263, 1935, 1495, 292, 1510, 1303, 2110]
          ![1490, 906, 1628, 232, 624, 768, 256, 128, 768, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1153, 161, 356, 1154, 1359, 1096, 1822, 713, 818, 692, 1350, 3087]
          ![1204, 1178, 1320, 232, 1520, 1568, 512, 256, 0, 1024, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1153, 1000, 356, 1154, 172, 122, 1743, 1615, 1792, 512, 1551, 3087]
          ![1536, 1024, 1248, 1120, 640, 1856, 128, 1536, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 13326720. -/
def representativePermutationSpinPlan13326720 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 0, 32, 768, 512, 256, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1456, 16, 0, 384, 896, 768, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1698, 1057, 1896, 1508, 1360, 672, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1896, 16, 0, 640, 384, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![4, 1, 2, 8, 480, 624, 192, 64, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 16, 32, 832, 640, 0, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![788, 1153, 546, 312, 1504, 1648, 1216, 1088, 256, 512, 1024, 2048]
          ![1, 1696, 1936, 1456, 48, 32, 768, 640, 1792, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![534, 2042, 586, 336, 1691, 1915, 1752, 1057, 256, 779, 1291, 2048]
          ![1460, 1150, 1260, 112, 336, 288, 768, 768, 1024, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2035, 672, 102, 963, 936, 458, 761, 1752, 256, 779, 1291, 2048]
          ![1885, 340, 1688, 272, 16, 960, 384, 128, 1536, 0, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![995, 154, 882, 1789, 1370, 274, 761, 1752, 256, 779, 1291, 2048]
          ![88, 298, 0, 856, 736, 672, 960, 896, 768, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![949, 16, 161, 1326, 1360, 402, 298, 1495, 527, 4, 1540, 2048]
          ![1228, 1466, 1288, 1416, 928, 544, 320, 768, 1792, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1898, 720, 1639, 1000, 1936, 1220, 122, 664, 527, 1362, 850, 2048]
          ![330, 462, 1400, 1936, 1616, 1856, 1472, 512, 1792, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1423, 768, 1639, 269, 1061, 1092, 298, 536, 234, 1362, 1253, 2048]
          ![1537, 1064, 996, 1056, 1600, 128, 128, 256, 0, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![270, 267, 1915, 1691, 256, 2027, 298, 536, 234, 1362, 1253, 2048]
          ![1039, 926, 12, 624, 304, 1792, 384, 256, 1536, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1277, 2038, 672, 2034, 1259, 768, 1753, 1217, 425, 1466, 1515, 2127]
          ![1895, 948, 1772, 360, 1536, 1248, 640, 1920, 1536, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![828, 1756, 864, 1754, 1533, 1789, 782, 1999, 691, 32, 278, 2971]
          ![305, 256, 1544, 512, 80, 448, 256, 0, 512, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![526, 5, 1040, 1072, 2007, 298, 1771, 292, 1706, 546, 554, 3087]
          ![557, 618, 1576, 1936, 800, 1152, 64, 128, 256, 1536, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![526, 1056, 1040, 1072, 64, 128, 214, 172, 1792, 512, 1551, 3087]
          ![14, 1036, 1032, 1024, 160, 192, 0, 0, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 18205440. -/
def representativePermutationSpinPlan18205440 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 8, 0, 32, 512, 384, 0, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 16, 32, 320, 896, 256, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![376, 1220, 402, 225, 1744, 1888, 1088, 1152, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1464, 480, 928, 704, 256, 1024, 1536, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1217, 292, 536, 818, 32, 48, 192, 1088, 256, 512, 1024, 2048]
          ![0, 2034, 1508, 1744, 48, 0, 64, 128, 768, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![81, 420, 504, 1090, 1056, 1072, 1216, 64, 256, 512, 1024, 2048]
          ![1041, 0, 1504, 1464, 672, 352, 704, 384, 1024, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![841, 154, 1898, 720, 1310, 1342, 610, 1220, 256, 782, 1294, 2048]
          ![1326, 792, 1748, 1808, 80, 544, 640, 256, 768, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![761, 1744, 906, 122, 32, 1310, 980, 1942, 256, 782, 1294, 2048]
          ![1327, 8, 448, 1024, 912, 416, 448, 896, 256, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![828, 536, 2007, 298, 1464, 1362, 980, 1942, 256, 782, 1294, 2048]
          ![0, 156, 180, 656, 816, 256, 512, 384, 1024, 1536, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1789, 298, 1277, 818, 738, 1706, 1045, 6, 2027, 1509, 997, 2048]
          ![739, 1462, 844, 1040, 1888, 1728, 1536, 1664, 768, 1536, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![2034, 963, 2042, 979, 234, 1719, 1045, 6, 2027, 1509, 997, 2048]
          ![242, 1470, 832, 200, 1424, 1760, 1088, 1024, 0, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![526, 2027, 1582, 519, 1218, 1999, 145, 466, 963, 1073, 1996, 2048]
          ![749, 236, 412, 1976, 1072, 256, 1472, 1664, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![270, 267, 2007, 1310, 781, 1218, 738, 643, 963, 1073, 1996, 2048]
          ![477, 220, 1912, 616, 560, 1056, 1408, 1664, 0, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1871, 1092, 113, 1088, 1487, 269, 1699, 1056, 882, 2042, 1730, 2487]
          ![1477, 854, 1268, 352, 1824, 1888, 1088, 1152, 1024, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![610, 1702, 336, 1706, 1090, 1359, 782, 1838, 756, 1000, 397, 2078]
          ![816, 516, 1532, 248, 896, 64, 768, 0, 512, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![3, 5, 1153, 1897, 1965, 738, 1999, 225, 1147, 480, 1007, 3087]
          ![2040, 1048, 516, 1000, 992, 1536, 1792, 1792, 1024, 1536, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![3, 1509, 1153, 1897, 949, 409, 172, 122, 1792, 512, 1551, 3087]
          ![1536, 1536, 480, 864, 128, 64, 640, 768, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 21331776. -/
def representativePermutationSpinPlan21331776 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1464, 0, 0, 640, 384, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1888, 0, 0, 384, 896, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 4, 8, 2, 32, 48, 192, 64, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 0, 32, 0, 0, 0, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1652, 1073, 1464, 1008, 1360, 128, 192, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 0, 32, 704, 384, 768, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![691, 889, 425, 32, 1789, 269, 1096, 1092, 256, 1629, 93, 2048]
          ![1387, 766, 1460, 360, 272, 32, 768, 512, 1536, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![889, 691, 32, 425, 949, 788, 1096, 1092, 256, 1629, 93, 2048]
          ![291, 766, 252, 888, 1344, 0, 64, 640, 768, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1756, 1744, 745, 864, 1942, 852, 738, 808, 527, 1362, 850, 2048]
          ![204, 1060, 1436, 1216, 944, 1536, 320, 512, 256, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![745, 864, 1756, 1744, 995, 145, 738, 808, 527, 1362, 850, 2048]
          ![559, 82, 1916, 880, 624, 1056, 1920, 1408, 1280, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![336, 794, 1698, 1008, 600, 713, 113, 857, 1582, 1435, 443, 3086]
          ![184, 82, 228, 456, 1520, 960, 1280, 256, 256, 0, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![794, 336, 1008, 1698, 1031, 1035, 113, 857, 1582, 1435, 443, 3086]
          ![893, 890, 956, 1216, 1568, 1280, 1728, 384, 1792, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![263, 1915, 271, 1117, 556, 1936, 1854, 32, 1582, 1536, 544, 3086]
          ![800, 1308, 512, 592, 256, 1152, 256, 768, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 21344741. -/
def representativePermutationSpinPlan21344741 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 0, 0, 576, 384, 0, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1456, 16, 32, 192, 128, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![469, 182, 1516, 356, 48, 1040, 1936, 480, 256, 512, 1024, 2048]
          ![1072, 1362, 1508, 8, 624, 448, 384, 768, 1024, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![182, 469, 356, 1516, 1696, 2032, 1936, 480, 256, 512, 1024, 2048]
          ![1072, 1362, 1508, 8, 96, 224, 128, 128, 1536, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![356, 1516, 182, 469, 1088, 128, 1936, 480, 256, 512, 1024, 2048]
          ![1072, 1360, 1508, 8, 880, 704, 704, 384, 0, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![2, 1059, 1075, 1360, 1423, 1487, 1941, 332, 256, 1871, 335, 2048]
          ![274, 1298, 648, 960, 2032, 352, 832, 384, 1024, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2034, 336, 995, 2035, 64, 1423, 652, 857, 256, 1871, 335, 2048]
          ![1746, 722, 328, 8, 1392, 32, 1088, 1536, 0, 1536, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![586, 882, 298, 672, 643, 214, 652, 857, 256, 1871, 335, 2048]
          ![1369, 244, 1744, 696, 256, 800, 0, 256, 1792, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![501, 1509, 828, 182, 1696, 610, 154, 1127, 1598, 113, 1649, 2048]
          ![1152, 2040, 1792, 1144, 1600, 0, 768, 1792, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![458, 1897, 841, 252, 209, 1043, 1771, 534, 1598, 113, 1649, 2048]
          ![763, 636, 1356, 944, 1552, 96, 1024, 1408, 768, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1999, 782, 1854, 1871, 1898, 889, 838, 336, 1975, 519, 1979, 3083]
          ![1615, 206, 124, 1200, 1408, 960, 1152, 128, 256, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![782, 1999, 1871, 1854, 923, 46, 838, 336, 1975, 519, 1979, 3083]
          ![1112, 220, 104, 1208, 880, 672, 320, 256, 1024, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1691, 1117, 1342, 1359, 9, 1065, 1698, 691, 1975, 1536, 956, 3083]
          ![640, 640, 144, 688, 1536, 192, 640, 0, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 21796800. -/
def representativePermutationSpinPlan21796800 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 0, 0, 576, 384, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1464, 16, 32, 192, 128, 768, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1508, 1896, 1057, 1698, 1936, 480, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1696, 1504, 1896, 16, 32, 960, 640, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![469, 1081, 355, 177, 1648, 1936, 1040, 1056, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 8, 624, 448, 448, 768, 1024, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1081, 469, 177, 355, 864, 432, 1040, 1056, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 8, 96, 224, 384, 896, 256, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![504, 946, 274, 192, 263, 1639, 3, 1941, 256, 1495, 983, 2048]
          ![2044, 602, 408, 608, 272, 768, 320, 128, 768, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![946, 504, 192, 274, 4, 1061, 3, 1941, 256, 1495, 983, 2048]
          ![808, 1934, 152, 608, 16, 800, 256, 384, 1280, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![310, 1696, 546, 1008, 1900, 1045, 1465, 2035, 1598, 745, 1257, 2048]
          ![413, 884, 1432, 8, 304, 1632, 1920, 1408, 1792, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![310, 214, 546, 1008, 298, 979, 1081, 12, 504, 720, 671, 2048]
          ![310, 430, 1916, 144, 16, 256, 832, 768, 1536, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1453, 838, 122, 1699, 1218, 402, 1077, 1081, 504, 720, 671, 2048]
          ![272, 2034, 116, 600, 336, 1408, 768, 768, 1792, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![6, 1504, 1468, 1900, 1008, 610, 1854, 775, 192, 946, 1842, 3087]
          ![1855, 546, 1800, 768, 672, 64, 512, 256, 1792, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1504, 6, 1900, 1468, 1038, 727, 1854, 775, 192, 946, 1842, 3087]
          ![2047, 1644, 1148, 184, 1584, 1216, 256, 1280, 512, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![526, 1566, 1975, 1383, 534, 298, 512, 1999, 192, 79, 1231, 3087]
          ![1032, 852, 400, 0, 288, 512, 640, 512, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 21808524. -/
def representativePermutationSpinPlan21808524 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 0, 32, 512, 256, 0, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1508, 1896, 0, 32, 960, 640, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1041, 1940, 1362, 1456, 720, 128, 192, 256, 512, 1024, 2048]
          ![1041, 1360, 1936, 1752, 0, 0, 384, 768, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1509, 534, 292, 1888, 1456, 1648, 1936, 256, 512, 1024, 2048]
          ![1, 2034, 1504, 1744, 544, 256, 576, 256, 1280, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![12, 5, 6, 4, 864, 432, 624, 912, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 512, 288, 512, 256, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2042, 979, 946, 102, 720, 864, 1008, 1360, 256, 512, 1024, 2048]
          ![1056, 2032, 1936, 0, 608, 448, 704, 384, 768, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1896, 4, 1940, 1088, 263, 2007, 182, 1363, 256, 1719, 183, 2048]
          ![859, 1162, 1048, 984, 640, 1376, 1472, 512, 1792, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![4, 1896, 1088, 1940, 177, 1075, 182, 1363, 256, 1719, 183, 2048]
          ![749, 906, 536, 984, 1424, 864, 1152, 1152, 512, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1653, 912, 564, 480, 745, 659, 570, 1366, 1533, 586, 1098, 2048]
          ![1599, 856, 116, 352, 1824, 1312, 1216, 0, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![692, 597, 172, 1660, 1822, 1179, 1900, 570, 1533, 586, 1098, 2048]
          ![36, 1750, 60, 8, 992, 352, 1792, 512, 512, 1024, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![692, 564, 172, 1660, 234, 1363, 336, 1453, 1077, 1045, 1067, 2048]
          ![207, 1628, 668, 328, 336, 1376, 1088, 1536, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1652, 756, 972, 284, 1059, 10, 1277, 336, 1077, 1045, 1067, 2048]
          ![207, 1630, 668, 1344, 528, 1728, 1280, 1408, 512, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1838, 1935, 779, 1822, 1660, 1654, 2034, 1698, 745, 355, 607, 2539]
          ![1327, 998, 124, 880, 320, 1184, 1024, 1408, 1536, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1935, 1838, 1822, 779, 871, 439, 2034, 1698, 745, 355, 607, 2539]
          ![1151, 1948, 120, 1488, 32, 1632, 1024, 128, 256, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1383, 1435, 523, 1566, 466, 234, 271, 2, 745, 62, 770, 2539]
          ![1334, 60, 304, 1072, 640, 896, 128, 768, 1536, 0, 0, 0])]

/-- Intermediate spin models for source permutation 32526135. -/
def representativePermutationSpinPlan32526135 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 16, 0, 768, 512, 256, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1041, 1362, 1940, 1752, 16, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1752, 16, 0, 128, 128, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![225, 402, 1220, 376, 1040, 32, 1088, 1152, 256, 512, 1024, 2048]
          ![1056, 1362, 0, 1456, 480, 896, 896, 640, 1280, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1653, 172, 972, 1648, 1326, 1342, 1896, 2, 256, 1822, 286, 2048]
          ![1311, 544, 1916, 880, 1968, 1408, 1728, 512, 1792, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1941, 624, 1948, 252, 16, 1326, 818, 586, 256, 1822, 286, 2048]
          ![1310, 274, 76, 1088, 16, 704, 1152, 768, 256, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![624, 1941, 252, 1948, 546, 122, 818, 586, 256, 1822, 286, 2048]
          ![1310, 1084, 888, 1656, 1056, 1472, 1408, 768, 1536, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1154, 1090, 10, 1898, 501, 713, 672, 1789, 256, 1453, 941, 2048]
          ![7, 1966, 928, 1080, 1120, 1824, 768, 128, 512, 512, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1888, 1898, 1127, 808, 234, 376, 581, 1915, 1679, 546, 1058, 2048]
          ![690, 60, 1684, 496, 1712, 960, 256, 1024, 768, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![972, 1654, 613, 390, 1224, 1370, 1639, 857, 1679, 546, 1058, 2048]
          ![1933, 108, 1000, 32, 1664, 128, 896, 1664, 1280, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![995, 1566, 613, 425, 1516, 1081, 1900, 570, 1696, 546, 1583, 2048]
          ![1073, 1724, 176, 1368, 1696, 512, 1344, 1792, 1280, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1154, 1696, 1466, 1654, 1362, 1073, 5, 1509, 1566, 1533, 1507, 2048]
          ![571, 1716, 76, 1408, 512, 992, 1088, 1152, 1792, 512, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![972, 425, 1466, 312, 1216, 1508, 1753, 1072, 336, 1533, 1872, 2048]
          ![1520, 848, 148, 1800, 432, 1568, 256, 384, 768, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![536, 713, 298, 1239, 92, 1464, 1653, 581, 1702, 1008, 1180, 2919]
          ![1702, 20, 1712, 176, 160, 960, 1856, 896, 1792, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![298, 1239, 536, 713, 1871, 1838, 1653, 581, 1702, 1008, 1180, 2919]
          ![0, 1634, 1632, 184, 464, 1248, 1408, 384, 512, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![393, 1465, 376, 425, 512, 783, 1147, 390, 1035, 349, 1585, 2919]
          ![206, 1116, 1176, 1216, 160, 704, 640, 512, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 33013198. -/
def representativePermutationSpinPlan33013198 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 8, 16, 0, 512, 256, 0, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 0, 0, 320, 768, 256, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 182, 355, 466, 432, 720, 336, 1696, 256, 512, 1024, 2048]
          ![1072, 1362, 1508, 8, 608, 480, 640, 256, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1362, 710, 906, 323, 128, 192, 2032, 336, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1744, 0, 0, 704, 256, 512, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![936, 841, 889, 432, 271, 1423, 963, 534, 256, 1871, 335, 2048]
          ![1704, 406, 1040, 680, 528, 512, 1216, 1280, 1792, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1224, 1456, 9, 1081, 1152, 271, 1366, 1045, 256, 1871, 335, 2048]
          ![1512, 1750, 852, 488, 320, 192, 1024, 1664, 512, 512, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1456, 1224, 1081, 9, 214, 597, 1366, 1045, 256, 1871, 335, 2048]
          ![447, 1228, 72, 1200, 1808, 192, 1536, 1536, 1280, 1024, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![501, 182, 469, 1509, 1915, 390, 1220, 1468, 1239, 664, 1176, 2048]
          ![1458, 432, 2040, 0, 992, 992, 256, 1152, 1280, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1648, 1366, 1061, 1936, 995, 1310, 92, 292, 1239, 664, 1176, 2048]
          ![578, 216, 8, 168, 1456, 1536, 1408, 896, 768, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![64, 312, 161, 788, 691, 32, 182, 912, 525, 1090, 578, 2048]
          ![422, 1460, 84, 584, 784, 288, 512, 640, 0, 1024, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![949, 1582, 161, 225, 1045, 613, 1509, 469, 504, 1090, 1525, 2048]
          ![1924, 1096, 1476, 1544, 1424, 1984, 1088, 1920, 1536, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1466, 504, 376, 312, 963, 390, 9, 12, 1582, 1435, 1461, 2048]
          ![1103, 1036, 1100, 1032, 0, 0, 640, 256, 0, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1072, 1089, 526, 1941, 972, 586, 10, 6, 841, 643, 15, 2539]
          ![1598, 704, 436, 776, 928, 448, 384, 640, 768, 1024, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![526, 1941, 1072, 1089, 512, 271, 10, 6, 841, 643, 15, 2539]
          ![1592, 390, 820, 704, 944, 480, 448, 512, 512, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1468, 1456, 393, 504, 2007, 1789, 1942, 525, 871, 685, 33, 2539]
          ![1524, 1536, 0, 592, 320, 576, 1408, 1280, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 33014936. -/
def representativePermutationSpinPlan33014936 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 0, 0, 512, 256, 0, 0, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1456, 16, 32, 128, 0, 768, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1508, 1896, 1057, 1698, 1936, 480, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1888, 16, 32, 896, 512, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2, 8, 4, 1, 672, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 16, 0, 512, 256, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1510, 92, 501, 420, 336, 672, 480, 1648, 256, 512, 1024, 2048]
          ![1040, 0, 1508, 1456, 416, 832, 896, 640, 512, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![390, 972, 581, 1652, 1360, 1696, 1504, 624, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1464, 784, 544, 448, 896, 1024, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![995, 889, 145, 1045, 1008, 1360, 1056, 1072, 256, 512, 1024, 2048]
          ![1041, 2032, 4, 1896, 992, 640, 896, 640, 0, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1698, 1652, 4, 1152, 1789, 269, 1509, 1465, 256, 1629, 93, 2048]
          ![698, 766, 1076, 1088, 832, 1728, 960, 1280, 768, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![738, 128, 980, 420, 2032, 1789, 1049, 12, 256, 1629, 93, 2048]
          ![794, 764, 404, 1512, 784, 544, 256, 128, 1792, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![808, 1089, 1359, 564, 161, 949, 1049, 12, 256, 1629, 93, 2048]
          ![536, 1362, 972, 1232, 752, 64, 256, 128, 512, 1536, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1915, 564, 1403, 1653, 501, 292, 586, 1468, 1383, 570, 1082, 2048]
          ![1459, 1188, 168, 1600, 1824, 640, 1152, 1920, 512, 1536, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![597, 1654, 692, 214, 788, 1935, 586, 1468, 1383, 570, 1082, 2048]
          ![1582, 6, 72, 1704, 1488, 1888, 448, 512, 512, 1024, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![610, 1743, 692, 225, 145, 1156, 504, 1719, 1360, 570, 1591, 2048]
          ![890, 354, 1472, 496, 1984, 1632, 704, 128, 512, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1898, 1360, 1059, 1654, 782, 5, 113, 32, 1743, 1197, 1122, 2048]
          ![357, 466, 740, 1792, 304, 320, 64, 768, 1536, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1871, 274, 1615, 738, 6, 3, 857, 889, 292, 852, 776, 2487]
          ![335, 12, 184, 1968, 240, 800, 0, 128, 256, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1615, 738, 1871, 274, 271, 263, 857, 889, 292, 852, 776, 2487]
          ![107, 14, 964, 1680, 496, 800, 256, 128, 768, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1043, 1075, 781, 1360, 2007, 270, 458, 1383, 491, 923, 967, 2487]
          ![1162, 760, 1760, 1440, 1184, 960, 512, 1024, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 35881849. -/
def representativePermutationSpinPlan35881849 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 16, 0, 576, 256, 256, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1752, 1940, 1362, 1041, 720, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1752, 16, 0, 448, 896, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1754, 1654, 1059, 1154, 1456, 720, 336, 672, 256, 512, 1024, 2048]
          ![1057, 2, 1648, 1744, 944, 608, 384, 896, 768, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![745, 1077, 113, 659, 1888, 1456, 1040, 1056, 256, 512, 1024, 2048]
          ![1073, 1698, 0, 1752, 736, 384, 896, 512, 1024, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1000, 1154, 546, 192, 2007, 1207, 2035, 1653, 256, 775, 1287, 2048]
          ![1228, 954, 1708, 1632, 784, 736, 64, 256, 1536, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1896, 1216, 1362, 2034, 864, 2007, 933, 310, 256, 775, 1287, 2048]
          ![284, 618, 888, 1640, 928, 928, 0, 512, 1792, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1216, 1896, 2034, 1362, 453, 1510, 933, 310, 256, 775, 1287, 2048]
          ![447, 204, 732, 1640, 688, 416, 0, 256, 1536, 0, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![214, 581, 390, 806, 1259, 1509, 252, 852, 1615, 1096, 584, 2048]
          ![1883, 858, 1372, 16, 16, 1600, 448, 1792, 1024, 1536, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1127, 1896, 154, 570, 1510, 453, 480, 980, 1743, 1224, 712, 2048]
          ![1582, 984, 956, 1632, 1664, 640, 1152, 1024, 1792, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1075, 393, 355, 963, 775, 1065, 788, 1941, 1743, 292, 1828, 2048]
          ![1365, 1944, 560, 920, 0, 576, 1280, 512, 1536, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![2027, 1743, 1533, 1885, 1089, 97, 1156, 779, 393, 1466, 1412, 2048]
          ![956, 1102, 748, 1640, 1408, 288, 64, 1920, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1092, 1220, 267, 4, 453, 1509, 256, 1679, 393, 1466, 1412, 2048]
          ![1141, 1722, 436, 888, 464, 64, 1856, 768, 1792, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1838, 1999, 1719, 781, 5, 1504, 1615, 192, 581, 32, 448, 2971]
          ![699, 1812, 1224, 1896, 1008, 928, 1600, 0, 768, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1719, 781, 1838, 1999, 672, 298, 1615, 192, 581, 32, 448, 2971]
          ![1680, 1392, 224, 1280, 992, 1312, 512, 128, 512, 0, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1156, 523, 1061, 1220, 154, 534, 1090, 504, 635, 30, 510, 2971]
          ![1924, 1368, 1080, 992, 1056, 960, 256, 768, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 42620160. -/
def representativePermutationSpinPlan42620160 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 0, 32, 576, 256, 256, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 16, 32, 256, 768, 0, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1057, 1508, 1896, 1698, 32, 1072, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1508, 1896, 16, 32, 192, 128, 768, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1362, 1940, 1041, 1752, 2032, 336, 128, 192, 256, 512, 1024, 2048]
          ![1041, 1362, 1940, 1752, 16, 0, 704, 384, 768, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![371, 1061, 409, 225, 1696, 2032, 1072, 1040, 256, 512, 1024, 2048]
          ![1057, 1360, 4, 1456, 1008, 640, 896, 512, 1024, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 1516, 1160, 1081, 336, 1696, 432, 720, 256, 512, 1024, 2048]
          ![1073, 1362, 1508, 0, 624, 448, 640, 256, 768, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1160, 1081, 1370, 1516, 128, 1216, 432, 720, 256, 512, 1024, 2048]
          ![1073, 1360, 1508, 0, 880, 704, 128, 128, 0, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![794, 122, 1008, 838, 1217, 1218, 857, 1000, 1147, 1915, 379, 2048]
          ![662, 790, 156, 96, 1984, 1984, 192, 1792, 1024, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1698, 310, 1696, 738, 1065, 371, 857, 1000, 1147, 1915, 379, 2048]
          ![663, 1604, 748, 8, 1632, 1152, 384, 1280, 1792, 0, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1090, 738, 564, 980, 469, 828, 1999, 1935, 527, 271, 1807, 2048]
          ![809, 1862, 832, 104, 736, 480, 576, 512, 1024, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![768, 527, 1435, 1147, 312, 864, 209, 32, 738, 1696, 1775, 2048]
          ![1326, 1454, 12, 1376, 16, 864, 384, 256, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1326, 1838, 1056, 225, 600, 312, 1370, 1948, 738, 1696, 1775, 2048]
          ![14, 1430, 236, 40, 1456, 1344, 576, 512, 512, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![841, 48, 409, 1057, 390, 2035, 1370, 1948, 738, 1696, 1775, 2048]
          ![1566, 10, 1704, 1200, 80, 1952, 1600, 1792, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![806, 323, 1008, 1360, 1056, 979, 1888, 252, 1871, 664, 1446, 2110]
          ![1475, 450, 648, 0, 1024, 1568, 768, 1920, 0, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![9, 1049, 1096, 1744, 672, 371, 284, 480, 1935, 512, 1664, 3087]
          ![1587, 162, 1000, 1968, 80, 192, 704, 256, 512, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1038, 1037, 491, 871, 979, 672, 1743, 128, 1935, 512, 1664, 3087]
          ![1164, 1548, 160, 160, 640, 1984, 640, 1280, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 42676038. -/
def representativePermutationSpinPlan42676038 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 16, 0, 704, 256, 512, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1698, 1508, 1896, 16, 0, 448, 768, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 4, 8, 2, 32, 48, 192, 64, 256, 512, 1024, 2048]
          ![0, 2, 4, 0, 16, 32, 64, 128, 0, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 284, 570, 808, 16, 32, 864, 1456, 256, 512, 1024, 2048]
          ![1, 1360, 1652, 1888, 800, 544, 0, 0, 768, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![393, 972, 586, 1464, 1040, 1056, 1888, 432, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1456, 784, 512, 128, 128, 1536, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![234, 376, 409, 1468, 1696, 2032, 1888, 432, 256, 512, 1024, 2048]
          ![1057, 1360, 0, 1456, 224, 128, 128, 0, 1792, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![691, 901, 1045, 48, 1117, 1789, 284, 1896, 256, 781, 1293, 2048]
          ![1622, 1966, 592, 1944, 400, 128, 576, 384, 768, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![659, 1072, 469, 581, 672, 1117, 312, 1156, 256, 781, 1293, 2048]
          ![1030, 1964, 0, 456, 592, 800, 960, 768, 256, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![241, 857, 1342, 933, 1065, 1516, 312, 1156, 256, 781, 1293, 2048]
          ![396, 2, 896, 808, 928, 352, 896, 256, 1024, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![2038, 586, 1789, 102, 1660, 1706, 1000, 64, 1239, 1754, 218, 2048]
          ![455, 1212, 76, 1064, 720, 1056, 1152, 1536, 1280, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1160, 312, 356, 1153, 1702, 1648, 818, 154, 1239, 1754, 218, 2048]
          ![1415, 1512, 684, 1992, 1808, 224, 320, 1152, 1280, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![263, 1117, 1359, 1487, 214, 1702, 1073, 469, 1239, 1754, 218, 2048]
          ![558, 952, 748, 1496, 2032, 640, 320, 1536, 0, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![525, 1239, 1743, 1615, 92, 1468, 1057, 597, 1117, 1370, 90, 2048]
          ![319, 1630, 368, 928, 1776, 384, 512, 1920, 1280, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1942, 933, 102, 1940, 1504, 92, 782, 1999, 1117, 1370, 90, 2048]
          ![1884, 1022, 1456, 1656, 1376, 576, 640, 1408, 1024, 1024, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![788, 949, 556, 332, 808, 154, 782, 1999, 1117, 1370, 90, 2048]
          ![389, 708, 888, 1048, 1488, 32, 704, 1152, 0, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1089, 1056, 1363, 9, 102, 252, 1935, 64, 1342, 267, 846, 2683]
          ![989, 1966, 4, 880, 2032, 864, 704, 1152, 1792, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1277, 1838, 512, 779, 1897, 1941, 192, 128, 469, 1075, 1807, 2775]
          ![353, 752, 1348, 976, 304, 864, 128, 1152, 1792, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1021, 1031, 685, 143, 252, 1897, 527, 271, 469, 1075, 1807, 2775]
          ![1704, 1332, 1056, 48, 288, 832, 512, 256, 1536, 0, 0, 0])]

/-- Intermediate spin models for source permutation 42831984. -/
def representativePermutationSpinPlan42831984 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 16, 0, 832, 640, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1464, 0, 32, 448, 768, 512, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1698, 1057, 1896, 1508, 1360, 672, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1888, 0, 32, 704, 256, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![4, 1, 2, 8, 480, 624, 192, 64, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 0, 0, 768, 512, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 1073, 1652, 2034, 432, 1744, 128, 192, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1456, 0, 0, 448, 896, 512, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1468, 1061, 1366, 1220, 1888, 432, 624, 912, 256, 512, 1024, 2048]
          ![1057, 1362, 4, 1464, 992, 640, 384, 896, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![794, 1699, 546, 310, 1744, 1888, 2032, 1360, 256, 512, 1024, 2048]
          ![1, 1698, 1940, 1456, 288, 800, 768, 512, 1280, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![536, 1220, 852, 64, 1207, 1639, 1510, 1059, 256, 775, 1287, 2048]
          ![1946, 1096, 364, 2008, 336, 768, 768, 896, 1024, 1024, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![209, 1487, 692, 610, 1366, 1092, 1510, 1059, 256, 775, 1287, 2048]
          ![326, 546, 576, 8, 608, 992, 448, 640, 256, 1024, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1217, 241, 128, 376, 882, 390, 1510, 1059, 256, 775, 1287, 2048]
          ![1612, 936, 284, 1208, 384, 160, 960, 256, 1024, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![371, 182, 274, 234, 336, 995, 1075, 3, 1383, 1888, 352, 2048]
          ![1461, 420, 884, 216, 1136, 608, 1600, 768, 512, 0, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1854, 241, 113, 393, 390, 882, 1360, 1898, 526, 9, 1545, 2048]
          ![1343, 804, 1004, 1992, 128, 384, 640, 384, 1536, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![912, 624, 92, 420, 775, 1160, 6, 1043, 526, 2035, 499, 2048]
          ![285, 390, 1892, 360, 16, 288, 512, 512, 1536, 512, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1533, 526, 1615, 1975, 889, 1000, 267, 512, 624, 480, 11, 2048]
          ![2016, 496, 1536, 448, 336, 576, 192, 896, 512, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![336, 1696, 1008, 1702, 145, 889, 745, 664, 624, 480, 11, 2048]
          ![1662, 12, 1032, 1512, 336, 736, 576, 896, 768, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![610, 1965, 458, 1699, 409, 371, 745, 664, 624, 480, 11, 2048]
          ![1905, 928, 1280, 16, 752, 576, 832, 384, 1024, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![393, 1342, 933, 581, 1008, 643, 536, 128, 1510, 356, 617, 3840]
          ![831, 1246, 8, 1488, 368, 736, 576, 1024, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![906, 2007, 828, 600, 16, 659, 376, 504, 1043, 2032, 992, 3086]
          ![1480, 1914, 1792, 1000, 272, 448, 704, 1408, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![349, 635, 1031, 207, 643, 16, 523, 1504, 1043, 2032, 992, 3086]
          ![216, 616, 400, 48, 576, 576, 768, 1536, 1536, 0, 0, 0])]

/-- Intermediate spin models for source permutation 49272960. -/
def representativePermutationSpinPlan49272960 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 0, 0, 0, 768, 640, 0, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1508, 1888, 0, 0, 704, 256, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1702, 1756, 1077, 1092, 1360, 672, 480, 624, 256, 512, 1024, 2048]
          ![1073, 1696, 4, 1744, 752, 384, 640, 384, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![710, 332, 901, 1940, 336, 1696, 1504, 1648, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1752, 768, 512, 384, 768, 0, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![355, 1081, 177, 469, 2032, 336, 1056, 48, 256, 512, 1024, 2048]
          ![1072, 1360, 1508, 8, 368, 960, 448, 896, 0, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![2, 1940, 1508, 1152, 1117, 1965, 1061, 761, 256, 1277, 765, 2048]
          ![859, 1790, 884, 416, 1072, 1728, 1728, 256, 1280, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1090, 128, 564, 1092, 1008, 1117, 857, 652, 256, 1277, 765, 2048]
          ![763, 1788, 1748, 8, 1120, 256, 1088, 1920, 512, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![128, 1090, 1092, 564, 425, 556, 857, 652, 256, 1277, 765, 2048]
          ![1374, 1788, 1160, 1696, 960, 608, 960, 1280, 1024, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![713, 1753, 172, 1756, 818, 102, 1888, 1639, 256, 1719, 183, 2048]
          ![1580, 602, 552, 616, 448, 896, 384, 640, 768, 1024, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1648, 1756, 779, 5, 1516, 469, 1698, 271, 1566, 425, 1961, 2048]
          ![79, 1640, 828, 672, 1728, 1120, 1216, 256, 1536, 1024, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1508, 1752, 2034, 1896, 581, 1660, 267, 1702, 1566, 425, 1961, 2048]
          ![901, 454, 348, 1360, 512, 1952, 64, 512, 1792, 1536, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![154, 1533, 2034, 534, 692, 214, 1156, 12, 864, 425, 894, 2048]
          ![165, 1698, 600, 1200, 128, 1600, 1024, 0, 512, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1533, 154, 534, 2034, 1360, 371, 1156, 12, 864, 425, 894, 2048]
          ![1056, 1698, 144, 848, 144, 736, 1024, 1408, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1154, 1000, 312, 145, 979, 672, 523, 519, 1495, 332, 1667, 2255]
          ![1727, 46, 56, 96, 944, 960, 448, 512, 512, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1061, 1900, 1756, 1936, 466, 882, 525, 10, 782, 512, 513, 3087]
          ![1583, 94, 2008, 984, 576, 608, 640, 896, 0, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![46, 30, 62, 1536, 672, 466, 214, 122, 782, 512, 513, 3087]
          ![14, 1664, 1944, 1456, 544, 256, 512, 768, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 57699840. -/
def representativePermutationSpinPlan57699840 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 0, 0, 512, 256, 0, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 16, 0, 320, 768, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1057, 1508, 1896, 1698, 32, 1072, 192, 64, 256, 512, 1024, 2048]
          ![1057, 1696, 1508, 1896, 16, 0, 128, 128, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1362, 1940, 1041, 1752, 2032, 336, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1752, 16, 32, 640, 384, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![371, 1061, 409, 225, 1696, 2032, 1072, 1040, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1456, 1008, 672, 960, 512, 1280, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1370, 1516, 1160, 1081, 336, 1696, 432, 720, 256, 512, 1024, 2048]
          ![1072, 1360, 1508, 0, 624, 480, 704, 256, 512, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![818, 225, 241, 64, 1117, 269, 1897, 1900, 256, 1453, 941, 2048]
          ![546, 94, 1080, 104, 512, 256, 832, 0, 1024, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![225, 818, 64, 241, 564, 972, 1897, 1900, 256, 1453, 941, 2048]
          ![230, 94, 592, 936, 528, 704, 1984, 1792, 0, 512, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![177, 241, 1854, 963, 3, 2, 182, 1366, 1582, 643, 1155, 2048]
          ![1278, 272, 1796, 1792, 448, 704, 256, 512, 1536, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1360, 402, 806, 570, 1152, 1153, 1077, 469, 1582, 643, 1155, 2048]
          ![148, 498, 736, 1872, 1424, 544, 64, 512, 512, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1360, 1370, 806, 570, 838, 1771, 409, 312, 1092, 4, 75, 2048]
          ![1663, 1276, 420, 1200, 1408, 928, 448, 1664, 0, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![323, 710, 1008, 355, 818, 154, 161, 409, 1092, 4, 75, 2048]
          ![543, 606, 64, 1936, 0, 32, 256, 768, 1280, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![64, 788, 1156, 1152, 570, 672, 48, 425, 564, 420, 264, 2775]
          ![798, 860, 1356, 1088, 224, 896, 768, 128, 1280, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![841, 949, 97, 453, 882, 466, 209, 376, 1403, 1654, 328, 2110]
          ![1598, 856, 328, 192, 256, 544, 768, 768, 256, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![995, 901, 613, 1043, 371, 161, 936, 720, 782, 512, 513, 3087]
          ![1566, 1540, 512, 704, 272, 416, 704, 896, 512, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![298, 828, 1239, 536, 466, 371, 685, 214, 782, 512, 513, 3087]
          ![270, 1140, 1400, 1888, 800, 768, 512, 768, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 71005440. -/
def representativePermutationSpinPlan71005440 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((8, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![0, 1696, 1936, 1464, 288, 768, 0, 128, 512, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![453, 838, 652, 1508, 1072, 1040, 1936, 480, 256, 512, 1024, 2048]
          ![1057, 1698, 1504, 1888, 272, 800, 192, 128, 1792, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![409, 234, 376, 1468, 32, 1072, 1744, 1888, 256, 512, 1024, 2048]
          ![1056, 1362, 0, 1456, 736, 384, 960, 512, 0, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1041, 1508, 4, 1216, 1326, 270, 1948, 1706, 256, 1854, 318, 2048]
          ![303, 1160, 1888, 424, 1488, 896, 0, 384, 256, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![145, 192, 756, 788, 1056, 1326, 1466, 6, 256, 1854, 318, 2048]
          ![302, 1946, 112, 696, 272, 800, 832, 896, 1024, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![882, 161, 546, 64, 420, 808, 1466, 6, 256, 1854, 318, 2048]
          ![286, 886, 532, 312, 144, 928, 576, 1792, 512, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1936, 556, 310, 852, 1089, 1088, 1059, 2032, 1147, 581, 1093, 2048]
          ![83, 754, 992, 1432, 1360, 512, 512, 128, 768, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1090, 1466, 1898, 1754, 4, 5, 102, 949, 1147, 581, 1093, 2048]
          ![1471, 1036, 1464, 0, 624, 448, 640, 384, 0, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![738, 1706, 1008, 336, 1, 4, 1423, 1000, 1147, 581, 1093, 2048]
          ![1470, 8, 896, 1024, 928, 608, 384, 768, 0, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1598, 1147, 1533, 1885, 720, 1468, 1259, 1509, 1706, 1096, 1765, 2048]
          ![318, 1456, 52, 2040, 16, 1216, 768, 0, 1280, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![241, 64, 852, 1487, 1900, 720, 1495, 1277, 1706, 1096, 1765, 2048]
          ![575, 1730, 720, 1264, 432, 1920, 768, 128, 0, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1756, 600, 1744, 664, 376, 936, 1854, 963, 838, 1008, 1556, 3087]
          ![1566, 804, 304, 1536, 0, 192, 320, 256, 256, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![600, 1756, 664, 1744, 1280, 923, 1854, 963, 838, 1008, 1556, 3087]
          ![1368, 80, 256, 1528, 1232, 1056, 1664, 1280, 1280, 512, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![600, 713, 664, 1744, 672, 979, 214, 635, 782, 512, 513, 3087]
          ![1296, 80, 328, 1968, 448, 768, 384, 512, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 71258152. -/
def representativePermutationSpinPlan71258152 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 0, 0, 704, 384, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1940, 1041, 1362, 1752, 1504, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1744, 16, 32, 896, 512, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1896, 1057, 1508, 1698, 1456, 1744, 128, 192, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1888, 0, 32, 384, 896, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1096, 97, 980, 946, 432, 720, 1152, 1216, 256, 512, 1024, 2048]
          ![1057, 2032, 1940, 8, 864, 704, 192, 0, 0, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![738, 113, 664, 1092, 1360, 672, 64, 1152, 256, 512, 1024, 2048]
          ![1073, 1696, 4, 1744, 480, 896, 384, 768, 1280, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1898, 652, 1900, 432, 1965, 1789, 788, 161, 256, 1629, 93, 2048]
          ![2, 1118, 1052, 24, 1792, 960, 768, 768, 0, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![10, 1456, 1660, 1948, 336, 1965, 81, 1045, 256, 1629, 93, 2048]
          ![243, 1116, 236, 1256, 544, 1504, 1728, 1280, 256, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1075, 1073, 16, 113, 1789, 336, 536, 692, 256, 1629, 93, 2048]
          ![434, 1118, 88, 8, 1088, 1568, 704, 1792, 1280, 0, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1756, 332, 761, 664, 154, 586, 241, 1999, 1147, 806, 1318, 2048]
          ![2000, 1062, 892, 976, 1776, 416, 1600, 1536, 1536, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1885, 1147, 1615, 1582, 1453, 794, 32, 889, 332, 1936, 1351, 2048]
          ![1757, 928, 156, 744, 1760, 768, 1152, 0, 256, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1117, 1487, 1259, 1342, 1719, 1453, 8, 1096, 332, 1936, 1351, 2048]
          ![784, 160, 888, 664, 272, 1632, 512, 640, 768, 0, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1464, 1216, 1940, 4, 1965, 512, 1370, 274, 713, 761, 282, 3069]
          ![1098, 862, 900, 784, 736, 352, 1728, 1408, 1280, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1216, 1464, 4, 1940, 62, 491, 1370, 274, 713, 761, 282, 3069]
          ![2, 878, 896, 1448, 1920, 1056, 0, 384, 1024, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1216, 1, 4, 1940, 97, 1090, 172, 635, 1888, 1081, 1187, 3069]
          ![1858, 1084, 1232, 1056, 1312, 1024, 1024, 512, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 77235657. -/
def representativePermutationSpinPlan77235657 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((8, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![1, 1698, 1936, 1456, 304, 800, 0, 128, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 570, 808, 284, 32, 48, 1744, 864, 256, 512, 1024, 2048]
          ![0, 1362, 1648, 1888, 816, 512, 0, 128, 768, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![177, 788, 756, 192, 270, 1326, 828, 122, 256, 1822, 286, 2048]
          ![303, 1656, 1456, 856, 1312, 1056, 576, 640, 1024, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![466, 64, 1153, 1154, 12, 1092, 838, 828, 256, 1822, 286, 2048]
          ![1310, 22, 368, 1648, 144, 96, 448, 256, 0, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![882, 1156, 1000, 1423, 852, 376, 838, 828, 256, 1822, 286, 2048]
          ![1040, 1500, 4, 1656, 1088, 1728, 1664, 512, 1024, 1024, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1754, 1696, 1898, 269, 1224, 1216, 1504, 534, 526, 1040, 528, 2048]
          ![1822, 6, 176, 528, 1696, 256, 1920, 1152, 0, 1536, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![779, 1156, 1900, 267, 376, 852, 1510, 1509, 1533, 995, 1507, 2048]
          ![1860, 1502, 660, 1512, 1904, 1376, 1920, 128, 1280, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![794, 738, 1965, 458, 1822, 901, 912, 1508, 1533, 818, 1330, 2048]
          ![398, 1066, 1300, 1512, 272, 704, 896, 1408, 768, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![794, 1696, 1965, 458, 1216, 8, 963, 32, 1648, 1403, 368, 2048]
          ![1814, 1220, 1148, 960, 608, 288, 384, 512, 256, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![122, 643, 610, 838, 192, 1000, 995, 963, 1648, 1403, 368, 2048]
          ![752, 1280, 148, 1288, 272, 544, 576, 896, 1536, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![81, 48, 613, 1822, 458, 546, 298, 745, 267, 4, 266, 3086]
          ![999, 266, 1476, 288, 864, 832, 0, 896, 0, 1536, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![30, 691, 1566, 425, 225, 453, 298, 745, 267, 4, 266, 3086]
          ![5, 106, 1400, 592, 160, 544, 768, 384, 1024, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![818, 336, 2038, 2034, 501, 48, 727, 62, 1691, 512, 276, 2191]
          ![784, 824, 768, 1040, 1088, 1792, 768, 512, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 79875840. -/
def representativePermutationSpinPlan79875840 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 0, 0, 768, 512, 256, 0, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1464, 16, 32, 384, 896, 768, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![794, 310, 1699, 546, 432, 1744, 1360, 672, 256, 512, 1024, 2048]
          ![1, 1698, 1940, 1456, 304, 768, 832, 512, 1024, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 838, 458, 643, 128, 192, 2032, 1360, 256, 512, 1024, 2048]
          ![1057, 1696, 1508, 1896, 16, 32, 640, 384, 512, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![536, 713, 761, 432, 271, 1423, 3, 1942, 256, 1871, 335, 2048]
          ![809, 1046, 400, 1824, 528, 512, 0, 512, 768, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![713, 536, 432, 761, 12, 1366, 3, 1942, 256, 1871, 335, 2048]
          ![1125, 602, 144, 1824, 784, 512, 0, 896, 1024, 1024, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![298, 864, 906, 600, 469, 652, 3, 1942, 256, 1871, 335, 2048]
          ![962, 288, 332, 616, 1616, 800, 1728, 1792, 512, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1948, 9, 1370, 1160, 453, 501, 1466, 2032, 527, 1088, 576, 2048]
          ![1744, 704, 1796, 472, 1536, 1664, 448, 768, 1280, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1719, 864, 234, 312, 652, 469, 10, 2, 1533, 946, 1458, 2048]
          ![1793, 632, 1796, 616, 656, 800, 896, 512, 1792, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![864, 1719, 312, 234, 1915, 613, 10, 2, 1533, 946, 1458, 2048]
          ![1794, 1084, 1796, 472, 640, 800, 960, 512, 1536, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![864, 409, 312, 234, 1088, 4, 336, 214, 1948, 263, 668, 2048]
          ![1617, 1204, 832, 616, 1600, 768, 1920, 1920, 1536, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![946, 979, 2042, 1789, 1468, 1464, 122, 172, 1179, 1435, 508, 2919]
          ![899, 1880, 1680, 464, 176, 672, 896, 256, 1536, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1021, 586, 818, 995, 161, 371, 122, 172, 1179, 1435, 508, 2919]
          ![1715, 856, 656, 360, 16, 768, 576, 256, 512, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![546, 794, 310, 1197, 672, 979, 727, 635, 782, 512, 513, 3087]
          ![512, 1568, 1792, 1280, 32, 512, 512, 768, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 80762880. -/
def representativePermutationSpinPlan80762880 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 16, 0, 576, 384, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1896, 16, 0, 896, 512, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![756, 161, 1154, 600, 1504, 624, 1216, 1088, 256, 512, 1024, 2048]
          ![1057, 0, 1652, 1744, 688, 320, 448, 768, 1280, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1000, 145, 1156, 882, 1456, 1744, 128, 1216, 256, 512, 1024, 2048]
          ![1041, 2032, 0, 1888, 480, 928, 640, 384, 0, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![92, 838, 534, 1504, 1639, 2007, 1218, 225, 256, 775, 1287, 2048]
          ![392, 12, 1036, 1208, 336, 544, 576, 768, 256, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![972, 480, 806, 1654, 432, 1639, 1153, 2035, 256, 775, 1287, 2048]
          ![1513, 108, 1132, 1200, 528, 704, 320, 128, 256, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![425, 1041, 48, 145, 2007, 432, 1092, 274, 256, 775, 1287, 2048]
          ![1128, 1166, 1084, 1208, 160, 640, 512, 256, 256, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1360, 6, 1059, 1154, 332, 828, 1088, 504, 1533, 2042, 506, 2048]
          ![833, 160, 876, 648, 1936, 1792, 256, 896, 1792, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![664, 1092, 808, 1089, 182, 710, 1466, 2, 1533, 2042, 506, 2048]
          ![919, 1224, 1436, 768, 464, 384, 960, 896, 1024, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1698, 794, 458, 1699, 1117, 371, 6, 1754, 1147, 1660, 124, 2048]
          ![194, 1068, 388, 928, 400, 1760, 320, 1792, 1024, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1698, 546, 458, 1699, 1744, 332, 692, 402, 1092, 267, 324, 2048]
          ![1197, 1538, 1892, 912, 1648, 1600, 576, 1536, 512, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![536, 64, 225, 818, 1940, 8, 1008, 214, 1092, 267, 324, 2048]
          ![278, 1984, 576, 696, 1600, 32, 1408, 1024, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![710, 466, 1366, 1117, 1224, 1216, 122, 172, 1871, 1090, 860, 2078]
          ![969, 2040, 120, 1984, 800, 192, 192, 896, 1536, 1536, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![349, 402, 234, 570, 161, 882, 122, 172, 1871, 1090, 860, 2078]
          ![1566, 500, 304, 192, 528, 544, 64, 640, 512, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![643, 610, 738, 1696, 672, 466, 727, 635, 782, 512, 513, 3087]
          ![1582, 1664, 824, 272, 0, 128, 128, 0, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 85327112. -/
def representativePermutationSpinPlan85327112 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 4, 8, 16, 32, 576, 256, 0, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 0, 32, 256, 768, 256, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 16, 0, 960, 512, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![597, 761, 1059, 161, 624, 1936, 1040, 32, 256, 512, 1024, 2048]
          ![1056, 2, 1648, 1744, 944, 608, 640, 256, 1024, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![534, 2034, 882, 2032, 1915, 267, 209, 425, 256, 1179, 667, 2048]
          ![1709, 1876, 892, 472, 176, 576, 512, 384, 768, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![128, 225, 64, 1218, 1117, 1342, 995, 1822, 1975, 556, 1068, 2048]
          ![1679, 1676, 596, 760, 160, 1728, 128, 1024, 512, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1362, 1896, 2, 1152, 980, 933, 691, 1045, 1975, 1207, 695, 2048]
          ![363, 1416, 8, 472, 1120, 1408, 1728, 640, 768, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![768, 1975, 1679, 525, 779, 1854, 122, 664, 1896, 570, 1589, 2048]
          ![304, 456, 1284, 904, 192, 1856, 1472, 1536, 1792, 1536, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1154, 1152, 1679, 1423, 1999, 1871, 828, 745, 234, 570, 909, 2048]
          ![20, 474, 912, 600, 512, 768, 768, 128, 512, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![292, 1508, 182, 652, 192, 1935, 1754, 1075, 794, 1468, 1807, 2078]
          ![11, 1478, 1080, 560, 64, 1984, 1408, 1792, 256, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![491, 356, 1509, 912, 527, 271, 1754, 1075, 794, 1468, 1807, 2078]
          ![674, 1648, 1192, 2032, 864, 640, 896, 768, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 85415649. -/
def representativePermutationSpinPlan85415649 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 0, 16, 32, 512, 384, 256, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1057, 1698, 1896, 480, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1698, 1504, 1888, 16, 32, 960, 512, 512, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1041, 1940, 1362, 1456, 720, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1362, 1940, 1744, 16, 0, 384, 896, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 1509, 534, 292, 1888, 1456, 1648, 1936, 256, 512, 1024, 2048]
          ![0, 2032, 1508, 1752, 560, 256, 576, 384, 1024, 1536, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1509, 828, 292, 534, 16, 32, 1648, 1936, 256, 512, 1024, 2048]
          ![0, 2032, 1508, 1752, 304, 800, 64, 0, 768, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![161, 546, 882, 64, 270, 1310, 6, 1468, 256, 1854, 318, 2048]
          ![287, 240, 1704, 944, 512, 256, 512, 128, 256, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![97, 1088, 274, 1090, 1040, 270, 652, 154, 256, 1854, 318, 2048]
          ![286, 960, 408, 1160, 432, 352, 64, 256, 1280, 1536, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1096, 1089, 504, 128, 1698, 1940, 652, 154, 256, 1854, 318, 2048]
          ![1342, 698, 1456, 808, 1392, 736, 448, 128, 1280, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![2032, 1510, 1466, 1218, 1041, 1152, 1897, 1888, 1885, 355, 1891, 2048]
          ![841, 160, 1520, 1432, 272, 1088, 512, 0, 0, 1536, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1466, 1218, 2032, 1510, 1359, 980, 1897, 1888, 1885, 355, 1891, 2048]
          ![534, 170, 664, 1224, 1632, 768, 512, 0, 256, 1536, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1598, 1885, 2027, 1533, 1744, 332, 1653, 1915, 1218, 376, 1397, 2048]
          ![318, 1938, 804, 712, 1888, 544, 576, 640, 1536, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![534, 1510, 2027, 469, 1752, 2007, 597, 480, 234, 376, 37, 2048]
          ![908, 954, 1660, 1584, 208, 1632, 1472, 1792, 0, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1057, 1059, 409, 225, 1259, 828, 390, 102, 1363, 1370, 563, 2919]
          ![1656, 1852, 1224, 904, 960, 1568, 1600, 128, 768, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![46, 453, 48, 161, 525, 1075, 390, 102, 1363, 1370, 563, 2919]
          ![1926, 816, 1312, 976, 608, 1600, 1792, 0, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 85835153. -/
def representativePermutationSpinPlan85835153 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 8, 0, 0, 512, 384, 256, 0, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1464, 16, 32, 128, 128, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1752, 1362, 1041, 1940, 1888, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1360, 1940, 1752, 0, 0, 384, 896, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1508, 1698, 1896, 1057, 1648, 1936, 128, 192, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1888, 16, 0, 960, 512, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![828, 298, 1753, 536, 480, 1648, 1456, 720, 256, 512, 1024, 2048]
          ![1, 2032, 1504, 1744, 560, 256, 512, 384, 1280, 1024, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![972, 586, 393, 1464, 1504, 624, 432, 1744, 256, 512, 1024, 2048]
          ![1072, 2034, 1652, 1456, 512, 256, 704, 384, 1024, 1024, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![393, 1464, 972, 586, 48, 1040, 432, 1744, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1456, 768, 544, 192, 0, 1536, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![453, 182, 534, 912, 1342, 270, 122, 600, 256, 1822, 286, 2048]
          ![318, 1222, 196, 1368, 816, 1792, 64, 768, 1024, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![949, 1936, 1942, 310, 1072, 1342, 376, 818, 256, 1822, 286, 2048]
          ![319, 998, 2020, 1656, 848, 992, 320, 0, 768, 1024, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1942, 310, 949, 1936, 284, 1652, 376, 818, 256, 1822, 286, 2048]
          ![318, 1714, 1452, 544, 0, 736, 1856, 0, 0, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![963, 393, 16, 1077, 172, 1915, 610, 1218, 1615, 81, 1617, 2048]
          ![707, 1224, 1088, 1808, 832, 1600, 1472, 128, 768, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![393, 963, 1077, 16, 1153, 1000, 610, 1218, 1615, 81, 1617, 2048]
          ![1122, 1558, 132, 976, 304, 1568, 1344, 1536, 512, 0, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1061, 523, 1077, 1468, 1935, 1154, 1216, 936, 995, 81, 940, 2048]
          ![1230, 1540, 888, 1488, 1776, 64, 1088, 128, 1024, 1536, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![393, 1468, 425, 1975, 271, 1965, 332, 432, 979, 97, 924, 2048]
          ![243, 1698, 1608, 1128, 2000, 1088, 704, 1920, 1280, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1940, 1936, 949, 980, 794, 1207, 745, 857, 2035, 2032, 533, 2539]
          ![869, 836, 1144, 1056, 512, 1440, 1280, 1280, 1536, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![923, 556, 710, 788, 1045, 523, 745, 857, 2035, 2032, 533, 2539]
          ![762, 936, 112, 1424, 736, 1024, 1024, 1024, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 85840916. -/
def representativePermutationSpinPlan85840916 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((8, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![1, 1696, 1940, 1464, 288, 800, 0, 128, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 570, 808, 284, 32, 48, 1744, 864, 256, 512, 1024, 2048]
          ![0, 1360, 1652, 1896, 800, 512, 0, 128, 512, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![808, 284, 1897, 570, 64, 1152, 1744, 864, 256, 512, 1024, 2048]
          ![1, 1360, 1652, 1896, 32, 32, 320, 896, 1536, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![209, 1043, 323, 1040, 1359, 271, 122, 828, 256, 1935, 399, 2048]
          ![1570, 544, 376, 1072, 384, 320, 128, 384, 0, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![225, 16, 979, 643, 1088, 1359, 252, 710, 256, 1935, 399, 2048]
          ![482, 1504, 700, 2032, 784, 32, 1216, 1280, 1024, 0, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![16, 225, 643, 979, 1468, 6, 252, 710, 256, 1935, 399, 2048]
          ![287, 1054, 1224, 136, 1152, 1920, 512, 768, 1792, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![92, 1516, 534, 838, 177, 1154, 480, 1691, 256, 779, 1291, 2048]
          ![453, 14, 1260, 1032, 592, 800, 256, 640, 0, 0, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![336, 838, 1453, 1706, 806, 570, 1041, 1310, 1975, 1468, 956, 2048]
          ![1564, 188, 200, 1072, 304, 832, 384, 896, 1024, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1654, 1942, 10, 781, 2038, 1900, 48, 713, 1975, 234, 1770, 2048]
          ![1254, 1132, 56, 1216, 1408, 1216, 960, 256, 256, 0, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![775, 519, 10, 1660, 1702, 1756, 1041, 889, 710, 234, 881, 2048]
          ![560, 1052, 1048, 120, 480, 352, 1280, 1664, 256, 1024, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1654, 1660, 806, 1147, 271, 1326, 1072, 857, 1179, 1719, 1324, 2048]
          ![376, 1894, 944, 528, 1728, 1120, 1408, 896, 1792, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1, 9, 782, 1465, 597, 1915, 1075, 1898, 102, 332, 858, 2539]
          ![20, 18, 1552, 1720, 880, 512, 1792, 768, 1280, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1038, 1653, 1217, 5, 1370, 519, 1075, 1898, 102, 332, 858, 2539]
          ![1598, 1096, 1888, 1648, 384, 640, 1152, 512, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 86528640. -/
def representativePermutationSpinPlan86528640 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 0, 0, 32, 512, 256, 0, 512, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1752, 1940, 1362, 1041, 720, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1752, 0, 32, 384, 896, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1073, 1652, 1464, 2034, 1056, 48, 192, 64, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1456, 16, 32, 192, 0, 768, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2, 4, 1, 8, 1008, 336, 128, 192, 256, 512, 1024, 2048]
          ![0, 0, 4, 0, 0, 0, 512, 384, 0, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![738, 1092, 113, 664, 2032, 1360, 1152, 1216, 256, 512, 1024, 2048]
          ![1073, 1698, 0, 1752, 480, 928, 384, 768, 1280, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1699, 1941, 1465, 1153, 672, 2032, 48, 16, 256, 512, 1024, 2048]
          ![1, 1696, 1936, 1456, 544, 288, 64, 128, 512, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![906, 664, 600, 864, 1965, 269, 1057, 1061, 256, 1277, 765, 2048]
          ![806, 942, 1156, 1608, 0, 768, 256, 256, 1280, 1024, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![332, 432, 122, 172, 209, 376, 4, 1057, 256, 1277, 765, 2048]
          ![763, 92, 320, 176, 1312, 192, 1280, 1408, 0, 1024, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1326, 267, 1965, 1915, 128, 402, 1896, 1940, 526, 2035, 499, 2048]
          ![1838, 1482, 284, 208, 1216, 704, 640, 640, 1280, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![267, 1326, 1915, 1965, 1510, 501, 1896, 1940, 526, 2035, 499, 2048]
          ![70, 1332, 1152, 184, 432, 576, 512, 1920, 1536, 0, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1179, 1127, 1403, 1453, 182, 1516, 1057, 4, 1239, 298, 1834, 2048]
          ![816, 1148, 88, 1176, 1328, 256, 320, 256, 1024, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1533, 1239, 1197, 1147, 6, 10, 161, 466, 1127, 252, 2044, 2048]
          ![1537, 94, 72, 16, 160, 192, 128, 128, 256, 1024, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1061, 761, 841, 949, 519, 525, 882, 672, 782, 512, 513, 3087]
          ![1583, 92, 2012, 976, 576, 576, 704, 896, 256, 1024, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![46, 1582, 16, 48, 122, 172, 882, 672, 782, 512, 513, 3087]
          ![14, 1664, 1944, 1456, 544, 256, 512, 768, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 87859296. -/
def representativePermutationSpinPlan87859296 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((14, false),
        representativeSpinRowsModel
          ![1940, 1752, 1041, 1362, 912, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1362, 1936, 1744, 0, 32, 960, 512, 768, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2034, 1464, 1652, 1073, 1696, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1456, 16, 32, 704, 384, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 8, 2, 4, 48, 16, 128, 192, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 0, 0, 64, 128, 0, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![97, 1096, 946, 980, 1072, 1040, 1152, 1216, 256, 512, 1024, 2048]
          ![1056, 2034, 1936, 8, 864, 736, 384, 768, 1024, 1024, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1092, 664, 113, 738, 912, 480, 64, 1152, 256, 512, 1024, 2048]
          ![1073, 1698, 0, 1752, 480, 896, 192, 0, 256, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![756, 600, 161, 1154, 1936, 1504, 1088, 128, 256, 512, 1024, 2048]
          ![1056, 0, 1652, 1744, 672, 352, 448, 896, 1024, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![209, 1041, 48, 1043, 12, 1077, 664, 564, 1533, 1789, 253, 2048]
          ![267, 1276, 404, 1944, 176, 864, 0, 0, 1024, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1092, 1088, 420, 274, 241, 1224, 613, 713, 1533, 1789, 253, 2048]
          ![83, 430, 1560, 8, 912, 1312, 1920, 768, 1536, 1536, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1092, 1871, 420, 274, 2007, 761, 882, 64, 972, 581, 1010, 2048]
          ![1388, 1002, 892, 240, 352, 896, 1024, 256, 1280, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![182, 92, 420, 1504, 1239, 536, 1152, 161, 1854, 581, 1349, 2048]
          ![2041, 498, 1040, 1440, 1120, 1152, 1920, 1152, 1024, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![527, 1464, 1073, 1652, 292, 828, 466, 371, 1277, 512, 1523, 3086]
          ![1577, 2034, 1948, 1024, 384, 960, 128, 384, 768, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1039, 1508, 1041, 8, 504, 1468, 466, 371, 1277, 512, 1523, 3086]
          ![1620, 496, 680, 1808, 704, 1920, 896, 1792, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 87922499. -/
def representativePermutationSpinPlan87922499 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 0, 0, 32, 576, 384, 0, 512, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 4, 8, 16, 32, 256, 896, 256, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1362, 1041, 1752, 1940, 336, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 16, 32, 640, 256, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![154, 284, 252, 432, 1117, 269, 1220, 1217, 256, 1453, 941, 2048]
          ![1938, 94, 124, 1144, 16, 256, 256, 128, 1280, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![2042, 1456, 1516, 12, 1360, 1117, 1073, 933, 256, 1453, 941, 2048]
          ![1891, 92, 1164, 136, 1584, 1024, 1984, 1408, 1280, 1024, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1065, 1370, 9, 1744, 972, 504, 1073, 933, 256, 1453, 941, 2048]
          ![1239, 764, 592, 1136, 848, 32, 1600, 1920, 512, 512, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1936, 4, 5, 1756, 1466, 720, 355, 16, 2027, 838, 1350, 2048]
          ![1611, 1658, 116, 280, 1776, 512, 704, 0, 1280, 512, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1629, 1370, 1363, 906, 504, 972, 1077, 469, 1582, 643, 1155, 2048]
          ![1763, 766, 736, 1072, 384, 736, 1984, 1280, 768, 512, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1370, 1629, 906, 1363, 995, 154, 1077, 469, 1582, 643, 1155, 2048]
          ![1659, 1822, 1948, 1504, 1312, 416, 448, 1792, 1280, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1370, 1360, 906, 1363, 838, 292, 1326, 1789, 1936, 1045, 1934, 2048]
          ![1117, 1768, 1100, 352, 736, 1920, 1856, 896, 1536, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1753, 332, 906, 1744, 2027, 534, 512, 1487, 1043, 1045, 24, 2048]
          ![1222, 730, 728, 1544, 1408, 736, 1984, 1408, 768, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![256, 1179, 1822, 779, 298, 828, 270, 1217, 1059, 1696, 1729, 2127]
          ![1289, 954, 648, 1976, 1968, 1952, 128, 640, 0, 512, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1792, 1495, 1854, 1127, 710, 1948, 270, 1217, 1059, 1696, 1729, 2127]
          ![1124, 756, 408, 640, 1728, 1216, 896, 1024, 512, 0, 0, 0])]

/-- Intermediate spin models for source permutation 106700773. -/
def representativePermutationSpinPlan106700773 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((10, false),
        representativeSpinRowsModel
          ![1896, 1698, 1057, 1508, 864, 1456, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1896, 16, 32, 384, 896, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1897, 1363, 1653, 1089, 1744, 864, 32, 48, 256, 512, 1024, 2048]
          ![0, 1360, 1648, 1888, 800, 544, 64, 0, 512, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1, 3, 9, 5, 64, 128, 16, 32, 256, 512, 1024, 2048]
          ![1, 0, 0, 8, 16, 32, 0, 0, 0, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![241, 1075, 857, 933, 1088, 1152, 1040, 1056, 256, 512, 1024, 2048]
          ![1073, 2, 1940, 1888, 672, 320, 704, 256, 1024, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![504, 1468, 556, 720, 1487, 1423, 1509, 1363, 256, 783, 1295, 2048]
          ![1746, 1936, 652, 1672, 288, 960, 0, 256, 1536, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1096, 1744, 1660, 1516, 64, 1487, 659, 310, 256, 783, 1295, 2048]
          ![274, 82, 332, 1352, 928, 640, 64, 512, 1280, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![252, 857, 284, 652, 1220, 1218, 122, 738, 1885, 1362, 850, 2048]
          ![1772, 1512, 744, 952, 1744, 0, 384, 1536, 512, 1536, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1495, 1744, 172, 828, 1487, 64, 458, 1008, 1615, 1088, 576, 2048]
          ![1582, 1900, 1020, 2040, 1632, 1824, 1088, 1408, 1536, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1342, 16, 469, 581, 783, 1152, 691, 1696, 1615, 128, 1664, 2048]
          ![686, 60, 1708, 1968, 1664, 32, 1216, 896, 768, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1743, 1615, 1147, 2027, 1360, 466, 1040, 782, 16, 1326, 1296, 2048]
          ![799, 204, 1368, 2000, 944, 1056, 0, 1280, 768, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![912, 581, 1147, 692, 906, 1629, 1941, 1153, 1359, 1326, 1377, 2048]
          ![1710, 1058, 1892, 1840, 1552, 704, 576, 128, 1536, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1504, 1702, 1468, 1936, 1495, 906, 1898, 1383, 1359, 1326, 1377, 2048]
          ![795, 236, 1164, 232, 1632, 0, 832, 0, 1280, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![781, 1696, 269, 1059, 1366, 1756, 652, 2027, 1089, 128, 129, 3087]
          ![421, 1230, 1564, 632, 144, 640, 960, 1536, 1536, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![570, 458, 808, 936, 1754, 6, 1771, 256, 1040, 9, 908, 2971]
          ![1229, 1604, 888, 944, 528, 800, 64, 128, 0, 1536, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![570, 284, 808, 936, 519, 1536, 1072, 1075, 534, 828, 858, 2971]
          ![298, 1096, 888, 352, 1536, 1792, 0, 0, 1024, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 106706497. -/
def representativePermutationSpinPlan106706497 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1464, 16, 0, 640, 256, 512, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1940, 1041, 1362, 1752, 1504, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1752, 0, 32, 960, 640, 768, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1896, 1057, 1508, 1698, 1456, 1744, 128, 192, 256, 512, 1024, 2048]
          ![1056, 1696, 1508, 1896, 16, 32, 448, 768, 512, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![252, 933, 1942, 852, 864, 1456, 1648, 912, 256, 512, 1024, 2048]
          ![1072, 2, 1940, 1888, 176, 96, 128, 128, 1792, 1536, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![154, 995, 882, 2038, 1744, 864, 1008, 1360, 256, 512, 1024, 2048]
          ![1040, 2034, 4, 1896, 224, 128, 128, 0, 1536, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1224, 852, 1220, 64, 1639, 1207, 806, 355, 256, 1495, 983, 2048]
          ![11, 984, 1068, 2000, 928, 1184, 64, 768, 512, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![963, 390, 2038, 882, 269, 271, 710, 1370, 2027, 828, 1340, 2048]
          ![1599, 1164, 804, 1088, 384, 128, 896, 640, 1792, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1117, 806, 234, 1008, 1073, 1075, 2042, 102, 2027, 828, 1340, 2048]
          ![289, 156, 1196, 1112, 1072, 768, 832, 768, 1024, 512, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![267, 1061, 1045, 12, 2, 1073, 128, 376, 2027, 828, 1340, 2048]
          ![503, 1884, 1772, 480, 1600, 1696, 1088, 1152, 1024, 0, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1239, 2027, 519, 1566, 972, 581, 808, 1898, 1061, 1326, 293, 2048]
          ![1917, 496, 680, 544, 992, 928, 896, 1920, 1792, 1024, 0, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1049, 12, 519, 1744, 214, 1654, 252, 857, 1259, 1326, 1221, 2048]
          ![1438, 1368, 2040, 1696, 1776, 64, 1088, 0, 1024, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![145, 64, 1935, 788, 1696, 214, 586, 1533, 1259, 1326, 1221, 2048]
          ![1096, 1438, 120, 376, 1648, 96, 1792, 0, 256, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1466, 376, 1207, 409, 756, 546, 995, 1566, 652, 828, 1108, 3087]
          ![1085, 1250, 480, 1024, 272, 608, 896, 640, 512, 0, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![390, 818, 534, 298, 794, 312, 1043, 525, 808, 570, 494, 2971]
          ![0, 1512, 1504, 2032, 784, 800, 0, 0, 256, 512, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![390, 2042, 534, 298, 1885, 1536, 1900, 1468, 1040, 691, 1318, 2971]
          ![1518, 1196, 104, 1120, 1984, 1856, 640, 1792, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 108582478. -/
def representativePermutationSpinPlan108582478 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 0, 8, 0, 0, 512, 256, 0, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1752, 1940, 1362, 1041, 720, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1744, 0, 0, 384, 896, 768, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1754, 1654, 1059, 1154, 1456, 720, 336, 672, 256, 512, 1024, 2048]
          ![1057, 2, 1648, 1752, 928, 608, 448, 896, 512, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1059, 1154, 1754, 1654, 1040, 32, 336, 672, 256, 512, 1024, 2048]
          ![1056, 2, 1648, 1744, 160, 96, 640, 384, 0, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1898, 1942, 1075, 1218, 1456, 1744, 336, 672, 256, 512, 1024, 2048]
          ![1073, 2, 1936, 1896, 928, 576, 384, 768, 512, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1465, 1089, 1217, 1072, 1639, 2007, 882, 390, 256, 775, 1287, 2048]
          ![1208, 92, 236, 1200, 896, 672, 384, 512, 1024, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![409, 48, 1057, 161, 432, 1639, 1510, 292, 256, 775, 1287, 2048]
          ![1240, 1084, 1160, 1208, 944, 160, 832, 640, 1280, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![48, 409, 161, 1057, 1366, 1092, 1510, 292, 256, 775, 1287, 2048]
          ![319, 734, 876, 1208, 928, 640, 64, 384, 768, 0, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![806, 214, 1652, 756, 1049, 1096, 624, 1259, 256, 779, 1291, 2048]
          ![1165, 1766, 1912, 2032, 544, 992, 512, 0, 768, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1326, 949, 1057, 161, 1224, 2042, 838, 182, 1598, 1077, 565, 2048]
          ![798, 360, 1960, 1376, 400, 32, 1216, 768, 512, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![97, 409, 979, 48, 1653, 1, 838, 182, 1598, 1077, 565, 2048]
          ![1719, 1322, 828, 360, 576, 64, 1856, 0, 1536, 0, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![995, 48, 32, 425, 546, 788, 775, 1629, 1615, 1092, 580, 2048]
          ![556, 1062, 876, 1568, 1600, 32, 768, 128, 1024, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![523, 1615, 1975, 1598, 1117, 1691, 1888, 458, 48, 979, 973, 2048]
          ![1995, 986, 144, 1288, 64, 320, 960, 256, 1024, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![5, 782, 1217, 9, 710, 1117, 1652, 972, 48, 979, 973, 2048]
          ![1349, 1670, 628, 600, 560, 1184, 1216, 1152, 1536, 1024, 0, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1224, 9, 1065, 775, 1088, 808, 600, 312, 1045, 2038, 2024, 2048]
          ![14, 1428, 692, 920, 1088, 704, 1792, 896, 1792, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1752, 1753, 1756, 298, 1888, 1096, 64, 376, 32, 1310, 800, 3584]
          ![289, 378, 428, 1088, 1344, 1824, 1536, 640, 1536, 0, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1000, 1153, 145, 1423, 664, 1744, 1216, 1464, 933, 355, 1528, 3840]
          ![15, 20, 512, 1552, 896, 1344, 1280, 128, 1536, 512, 0, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1000, 756, 145, 1423, 234, 439, 469, 828, 1218, 128, 909, 3840]
          ![1906, 2024, 128, 2032, 736, 1472, 1408, 1536, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 121567626. -/
def representativePermutationSpinPlan121567626 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2032, 1652, 1456, 16, 32, 640, 256, 512, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1896, 1508, 1698, 1057, 1744, 864, 64, 128, 256, 512, 1024, 2048]
          ![1056, 1698, 1508, 1896, 16, 32, 384, 768, 512, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![154, 2038, 995, 882, 1456, 1744, 1360, 1696, 256, 512, 1024, 2048]
          ![1041, 2034, 4, 1888, 240, 128, 192, 128, 1792, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![10, 6, 3, 2, 432, 720, 336, 672, 256, 512, 1024, 2048]
          ![0, 2, 0, 8, 256, 768, 768, 512, 512, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![3, 2, 10, 6, 16, 32, 336, 672, 256, 512, 1024, 2048]
          ![1, 2, 0, 0, 528, 288, 0, 128, 0, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![841, 284, 1900, 1888, 270, 1310, 534, 946, 256, 1854, 318, 2048]
          ![286, 160, 472, 1496, 640, 320, 0, 384, 1024, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![284, 841, 1888, 1900, 536, 402, 534, 946, 256, 1854, 318, 2048]
          ![286, 1160, 1264, 1992, 1712, 576, 0, 128, 1280, 512, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![458, 720, 570, 889, 1940, 8, 534, 946, 256, 1854, 318, 2048]
          ![302, 758, 308, 448, 432, 1664, 832, 1280, 512, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![664, 828, 906, 713, 4, 1652, 586, 336, 526, 1072, 560, 2048]
          ![544, 1490, 1108, 96, 848, 832, 1024, 256, 1280, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![828, 664, 713, 906, 64, 788, 586, 336, 526, 1072, 560, 2048]
          ![544, 176, 1284, 1288, 768, 288, 512, 256, 1792, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1453, 1719, 1822, 1629, 756, 1423, 946, 534, 1383, 857, 1369, 2048]
          ![825, 6, 152, 104, 224, 1984, 128, 1152, 256, 1024, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1598, 1383, 1885, 1566, 292, 1487, 97, 597, 1719, 794, 1050, 2048]
          ![4, 170, 412, 944, 1184, 1984, 576, 0, 256, 0, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![933, 102, 1942, 980, 1259, 292, 1756, 1366, 1719, 794, 1050, 2048]
          ![1854, 4, 140, 2032, 1424, 960, 896, 384, 1792, 1024, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1948, 949, 852, 252, 1040, 3, 1756, 1366, 1719, 794, 1050, 2048]
          ![633, 600, 116, 1472, 992, 1568, 1600, 1792, 1792, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![713, 761, 864, 122, 1942, 1941, 12, 1370, 1277, 512, 902, 2683]
          ![301, 1440, 744, 1824, 528, 0, 832, 640, 1792, 1024, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![761, 713, 122, 864, 871, 207, 12, 1370, 1277, 512, 902, 2683]
          ![1142, 348, 1456, 1152, 928, 1344, 640, 1792, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 149929934. -/
def representativePermutationSpinPlan149929934 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((8, false),
        representativeSpinRowsModel
          ![1941, 310, 556, 788, 48, 16, 912, 1504, 256, 512, 1024, 2048]
          ![0, 1696, 1940, 1456, 288, 768, 64, 128, 512, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![453, 838, 652, 1508, 1072, 1040, 1936, 480, 256, 512, 1024, 2048]
          ![1057, 1698, 1508, 1896, 272, 800, 128, 128, 1792, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![409, 234, 376, 1468, 32, 1072, 1744, 1888, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1464, 736, 384, 896, 512, 0, 1536, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1041, 1508, 4, 1216, 1326, 270, 1948, 1706, 256, 1854, 318, 2048]
          ![303, 1160, 1892, 416, 1488, 896, 64, 384, 256, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1152, 1752, 1, 1896, 1466, 6, 1948, 1706, 256, 1854, 318, 2048]
          ![1342, 1054, 1064, 136, 432, 416, 192, 1024, 512, 0, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![643, 949, 1056, 841, 1218, 1043, 1744, 1160, 1615, 113, 1649, 2048]
          ![1689, 242, 392, 1904, 1696, 128, 1600, 768, 768, 1024, 0, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1495, 1752, 1753, 432, 6, 1466, 1065, 1096, 1679, 177, 1713, 2048]
          ![1336, 242, 144, 216, 1104, 448, 1280, 1152, 768, 0, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1936, 480, 252, 1941, 1854, 393, 263, 1049, 1679, 1154, 642, 2048]
          ![415, 568, 280, 408, 1856, 416, 960, 1536, 256, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1897, 1383, 252, 1900, 745, 32, 1065, 1456, 1654, 1154, 1785, 2048]
          ![685, 564, 12, 1848, 928, 864, 1536, 1408, 1792, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![570, 857, 154, 1127, 1615, 2027, 1065, 1456, 1654, 1154, 1785, 2048]
          ![1385, 406, 1796, 1224, 448, 256, 1280, 1664, 512, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![97, 16, 1059, 161, 652, 1383, 1370, 234, 214, 1648, 1219, 2078]
          ![1855, 434, 1456, 0, 1872, 480, 1856, 1024, 512, 512, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1516, 1081, 1660, 12, 1582, 841, 274, 504, 1965, 1698, 1186, 3840]
          ![1526, 46, 496, 592, 1056, 576, 320, 640, 0, 512, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1648, 12, 1702, 1077, 1360, 1218, 600, 312, 1259, 1508, 2020, 3840]
          ![1904, 1112, 656, 528, 896, 1472, 1152, 0, 0, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 160152960. -/
def representativePermutationSpinPlan160152960 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 4, 8, 16, 32, 768, 512, 0, 0, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1464, 1652, 2034, 1073, 1744, 1888, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1652, 1464, 0, 0, 384, 896, 512, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![794, 310, 1699, 546, 432, 1744, 1360, 672, 256, 512, 1024, 2048]
          ![0, 1696, 1940, 1456, 288, 800, 832, 512, 1280, 1536, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![906, 710, 323, 1362, 1456, 720, 336, 1696, 256, 512, 1024, 2048]
          ![1041, 1360, 1936, 1752, 256, 800, 960, 640, 1024, 1536, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![323, 1362, 906, 710, 16, 1056, 336, 1696, 256, 512, 1024, 2048]
          ![1040, 1360, 1936, 1744, 528, 256, 128, 128, 1536, 512, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![393, 92, 556, 864, 1310, 270, 214, 738, 256, 1838, 302, 2048]
          ![287, 1506, 1160, 136, 1824, 1056, 832, 128, 1024, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1464, 1456, 425, 312, 2038, 1756, 564, 214, 256, 1838, 302, 2048]
          ![318, 792, 0, 1664, 112, 1280, 1536, 1664, 1536, 0, 0, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![376, 1468, 234, 1207, 1516, 10, 564, 214, 256, 1838, 302, 2048]
          ![1056, 906, 1004, 1384, 304, 448, 448, 128, 768, 1024, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![546, 192, 466, 1423, 2042, 1888, 1648, 692, 1566, 48, 1584, 2048]
          ![830, 696, 608, 880, 1456, 1344, 0, 0, 768, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![192, 546, 1423, 466, 1940, 1508, 1648, 692, 1566, 48, 1584, 2048]
          ![830, 14, 1740, 456, 1872, 1280, 64, 1664, 768, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1999, 779, 512, 1629, 1896, 1073, 214, 564, 1975, 409, 1945, 2048]
          ![1557, 1084, 1892, 1872, 1456, 192, 1024, 1280, 0, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1582, 1975, 1885, 768, 980, 933, 1699, 1897, 779, 1220, 964, 2048]
          ![1748, 936, 1896, 112, 1920, 896, 1024, 1920, 256, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![453, 912, 828, 838, 113, 980, 882, 672, 779, 1220, 964, 2048]
          ![1536, 142, 992, 960, 16, 800, 0, 768, 0, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![177, 756, 1156, 64, 624, 420, 979, 371, 782, 512, 513, 3087]
          ![1598, 140, 1256, 688, 576, 320, 640, 768, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 203638538. -/
def representativePermutationSpinPlan203638538 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 8, 0, 0, 512, 256, 0, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1754, 761, 172, 600, 1008, 336, 720, 1888, 256, 512, 1024, 2048]
          ![1057, 0, 1652, 1752, 928, 608, 448, 896, 512, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![828, 536, 298, 1753, 1936, 480, 720, 1888, 256, 512, 1024, 2048]
          ![1, 2034, 1504, 1752, 544, 256, 512, 384, 1024, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![1366, 355, 1363, 672, 1259, 1915, 841, 1000, 256, 1179, 667, 2048]
          ![1095, 68, 1692, 656, 896, 896, 1600, 512, 768, 512, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![6, 1696, 1043, 1059, 912, 1259, 664, 1089, 256, 1179, 667, 2048]
          ![311, 1332, 1688, 992, 1520, 1856, 320, 512, 1024, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1043, 1059, 6, 1696, 586, 818, 664, 1089, 256, 1179, 667, 2048]
          ![885, 1004, 1692, 168, 1696, 1856, 1472, 256, 1792, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1509, 828, 1504, 838, 154, 1789, 97, 81, 527, 1940, 404, 2048]
          ![748, 610, 32, 568, 1296, 416, 1792, 512, 256, 1024, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![1504, 838, 1509, 828, 1360, 1218, 97, 81, 527, 1940, 404, 2048]
          ![130, 512, 116, 592, 688, 1056, 1280, 640, 256, 1024, 1024, 0]),
      ((3, false),
        representativeSpinRowsModel
          ![1504, 92, 1509, 828, 901, 1310, 1896, 1898, 979, 371, 654, 2048]
          ![629, 390, 1912, 160, 192, 1600, 576, 1408, 512, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![356, 469, 624, 420, 214, 172, 2, 1896, 979, 371, 654, 2048]
          ![1604, 390, 236, 352, 16, 544, 576, 640, 512, 1536, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1696, 1075, 1059, 1360, 828, 912, 1152, 1000, 2035, 995, 1002, 3079]
          ![431, 1454, 1000, 672, 656, 128, 960, 0, 1024, 0, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1752, 1073, 2034, 1041, 1654, 1510, 546, 458, 270, 5, 1354, 2127]
          ![248, 1818, 664, 2032, 0, 224, 64, 256, 1792, 0, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![756, 177, 1153, 1156, 1508, 2, 122, 432, 1487, 512, 914, 2397]
          ![740, 1944, 1760, 464, 192, 640, 640, 0, 1536, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 204631599. -/
def representativePermutationSpinPlan204631599 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![1, 2, 0, 8, 0, 0, 512, 256, 0, 512, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![8, 4, 2, 1, 720, 864, 64, 128, 256, 512, 1024, 2048]
          ![1, 0, 0, 0, 16, 0, 320, 768, 256, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1652, 1464, 1073, 2034, 1936, 1504, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2032, 1648, 1456, 0, 32, 896, 512, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1220, 376, 225, 402, 912, 480, 1088, 1152, 256, 512, 1024, 2048]
          ![1056, 1362, 4, 1464, 496, 928, 192, 128, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![818, 536, 292, 1217, 1696, 1008, 192, 1088, 256, 512, 1024, 2048]
          ![0, 2034, 1504, 1752, 48, 32, 576, 384, 1792, 1024, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![738, 664, 1092, 113, 672, 2032, 1216, 64, 256, 512, 1024, 2048]
          ![1073, 1696, 4, 1744, 480, 896, 384, 768, 1024, 1024, 0, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![710, 1941, 933, 1936, 1965, 269, 209, 376, 256, 1277, 765, 2048]
          ![999, 942, 2016, 472, 464, 896, 704, 0, 768, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![182, 912, 453, 501, 1696, 1965, 808, 857, 256, 1277, 765, 2048]
          ![1463, 940, 432, 896, 1952, 576, 1728, 0, 512, 0, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![912, 182, 501, 453, 1160, 9, 808, 857, 256, 1277, 765, 2048]
          ![1950, 940, 668, 1368, 1408, 1408, 1216, 768, 1280, 1024, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![48, 453, 1838, 371, 1359, 2007, 1942, 1075, 1147, 390, 1926, 2048]
          ![1159, 1902, 72, 2032, 736, 1792, 832, 1408, 512, 512, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![269, 1510, 10, 1898, 713, 81, 16, 949, 1147, 390, 1926, 2048]
          ![1939, 1276, 592, 944, 640, 128, 384, 256, 768, 1024, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1533, 1147, 1383, 519, 852, 128, 1073, 1752, 1510, 1259, 230, 2048]
          ![286, 1278, 1600, 856, 1280, 352, 1024, 128, 768, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![933, 581, 469, 1342, 1615, 1743, 2034, 298, 1466, 1154, 1307, 2094]
          ![1039, 1692, 12, 400, 1552, 1600, 704, 896, 512, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![62, 1598, 1077, 1854, 284, 1660, 2034, 298, 1466, 1154, 1307, 2094]
          ![15, 668, 12, 624, 16, 768, 0, 128, 1280, 512, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![779, 1468, 1077, 1035, 1915, 172, 672, 2042, 1679, 1154, 684, 2094]
          ![2036, 1576, 1568, 1936, 416, 256, 128, 1280, 0, 0, 0, 0])]

/-- Intermediate spin models for source permutation 206934638. -/
def representativePermutationSpinPlan206934638 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((13, false),
        representativeSpinRowsModel
          ![2034, 1073, 1464, 1652, 1360, 1696, 64, 128, 256, 512, 1024, 2048]
          ![1073, 2034, 1652, 1456, 16, 32, 640, 384, 768, 512, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1940, 1041, 1362, 1752, 1504, 1648, 192, 64, 256, 512, 1024, 2048]
          ![1041, 1360, 1940, 1744, 0, 0, 960, 512, 512, 512, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1156, 145, 882, 1000, 480, 624, 1216, 1088, 256, 512, 1024, 2048]
          ![1040, 2034, 0, 1896, 480, 896, 128, 0, 0, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![214, 122, 458, 336, 267, 1259, 8, 1073, 256, 1179, 667, 2048]
          ![565, 1132, 236, 104, 0, 256, 0, 256, 256, 1536, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![806, 1360, 234, 1370, 1504, 267, 161, 841, 256, 1179, 667, 2048]
          ![1700, 1276, 232, 248, 208, 672, 832, 640, 1024, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![177, 882, 312, 1160, 1045, 1756, 371, 1838, 1383, 252, 1788, 2048]
          ![686, 802, 784, 216, 0, 608, 1984, 384, 0, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![1061, 979, 453, 225, 745, 32, 1935, 466, 1383, 252, 1788, 2048]
          ![292, 1312, 668, 2040, 992, 1664, 512, 896, 1536, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![292, 2027, 453, 1504, 659, 355, 756, 145, 102, 252, 769, 2048]
          ![466, 1474, 664, 1864, 624, 832, 896, 896, 1792, 0, 1024, 0]),
      ((7, false),
        representativeSpinRowsModel
          ![1061, 1504, 1936, 523, 1915, 512, 1088, 1041, 818, 936, 85, 2048]
          ![1172, 1548, 12, 1656, 192, 1440, 576, 1792, 768, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![564, 420, 128, 808, 779, 267, 1057, 48, 298, 672, 1136, 3079]
          ![565, 222, 2028, 1992, 512, 640, 64, 256, 768, 1536, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![79, 1092, 1090, 113, 624, 2027, 1057, 48, 298, 672, 1136, 3079]
          ![384, 194, 116, 176, 976, 576, 0, 1024, 1280, 0, 1024, 0]),
      ((2, false),
        representativeSpinRowsModel
          ![1075, 1754, 1090, 1037, 652, 501, 161, 1582, 1366, 672, 684, 3079]
          ![1952, 1960, 264, 496, 224, 960, 0, 0, 1024, 0, 0, 0])]

/-- Intermediate spin models for source permutation 221802288. -/
def representativePermutationSpinPlan221802288 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 0, 0, 832, 512, 256, 512, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1896, 0, 0, 640, 384, 512, 512, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![806, 613, 597, 912, 1965, 269, 1153, 1160, 256, 1277, 765, 2048]
          ![534, 942, 1556, 1056, 272, 288, 0, 768, 1280, 1536, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![284, 480, 214, 172, 113, 469, 9, 1153, 256, 1277, 765, 2048]
          ![858, 92, 224, 280, 1424, 1408, 1408, 0, 0, 1536, 1024, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1423, 263, 1965, 2007, 32, 355, 1941, 1897, 527, 2034, 498, 2048]
          ![900, 1334, 120, 320, 752, 704, 1024, 512, 1280, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![263, 1423, 2007, 1965, 1466, 504, 1941, 1897, 527, 2034, 498, 2048]
          ![273, 1480, 228, 1064, 656, 1856, 448, 512, 1536, 512, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1127, 1179, 1495, 1453, 234, 1468, 1153, 9, 1147, 390, 1926, 2048]
          ![801, 1244, 1132, 88, 256, 288, 1472, 256, 1024, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1533, 1147, 1197, 1239, 10, 6, 161, 371, 1179, 252, 2044, 2048]
          ![1536, 94, 72, 24, 176, 192, 128, 0, 256, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![1160, 756, 788, 1000, 523, 525, 979, 672, 783, 512, 513, 3086]
          ![735, 92, 888, 1904, 736, 768, 512, 512, 256, 1536, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![177, 145, 1154, 546, 420, 624, 979, 672, 783, 512, 513, 3086]
          ![94, 1116, 56, 688, 800, 384, 768, 512, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 232446768. -/
def representativePermutationSpinPlan232446768 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((11, false),
        representativeSpinRowsModel
          ![2, 1, 8, 4, 336, 672, 64, 128, 256, 512, 1024, 2048]
          ![0, 2, 0, 0, 0, 0, 576, 384, 256, 512, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![1073, 2034, 1652, 1464, 1040, 1056, 64, 128, 256, 512, 1024, 2048]
          ![1072, 2034, 1648, 1456, 16, 32, 192, 128, 512, 0, 0, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![1508, 1896, 1057, 1698, 1936, 480, 64, 128, 256, 512, 1024, 2048]
          ![1057, 1698, 1508, 1888, 16, 32, 960, 640, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![2, 8, 4, 1, 672, 1008, 192, 64, 256, 512, 1024, 2048]
          ![1, 2, 0, 0, 16, 0, 576, 384, 0, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1510, 92, 501, 420, 336, 672, 480, 1648, 256, 512, 1024, 2048]
          ![1040, 0, 1504, 1456, 416, 832, 960, 512, 768, 0, 0, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![390, 972, 581, 1652, 1360, 1696, 1504, 624, 256, 512, 1024, 2048]
          ![1073, 2034, 1648, 1464, 784, 544, 384, 768, 1280, 0, 0, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![581, 1652, 390, 972, 1056, 48, 1504, 624, 256, 512, 1024, 2048]
          ![1072, 2032, 1648, 1464, 256, 800, 128, 128, 512, 1024, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![3, 1898, 1466, 2032, 1342, 1310, 1516, 292, 256, 1838, 302, 2048]
          ![1327, 2010, 564, 984, 1200, 128, 1984, 1152, 1536, 1536, 1024, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![1898, 3, 2032, 1466, 466, 788, 1516, 292, 256, 1838, 302, 2048]
          ![1327, 566, 500, 280, 1200, 864, 128, 768, 1280, 0, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![536, 1744, 298, 864, 145, 1156, 1509, 652, 1147, 597, 1109, 2048]
          ![1364, 24, 784, 1040, 1312, 704, 256, 1536, 256, 0, 1024, 0]),
      ((14, false),
        representativeSpinRowsModel
          ![332, 664, 1756, 906, 1075, 963, 1509, 652, 1147, 597, 1109, 2048]
          ![1365, 54, 36, 1280, 1456, 544, 832, 256, 256, 1536, 1024, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1582, 1147, 1885, 523, 720, 586, 782, 781, 664, 980, 259, 2048]
          ![814, 784, 576, 2032, 288, 864, 64, 0, 1792, 1024, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![225, 292, 1224, 1217, 154, 720, 145, 466, 664, 980, 259, 2048]
          ![288, 1102, 268, 1832, 832, 192, 448, 0, 1280, 512, 0, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![995, 501, 81, 901, 376, 936, 161, 371, 1495, 1756, 482, 2110]
          ![1599, 142, 404, 784, 16, 32, 512, 0, 256, 1536, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![312, 356, 600, 1156, 889, 209, 979, 672, 783, 512, 513, 3086]
          ![2, 642, 1192, 168, 368, 608, 320, 512, 512, 1024, 0, 0]),
      ((11, false),
        representativeSpinRowsModel
          ![356, 312, 1156, 600, 933, 113, 979, 672, 783, 512, 513, 3086]
          ![162, 544, 1544, 512, 864, 320, 768, 768, 512, 1024, 0, 0])]

/-- Intermediate spin models for source permutation 237253688. -/
def representativePermutationSpinPlan237253688 : RepresentativeSpinPlan RepresentativeNodeLetter :=
  [
      ((12, false),
        representativeSpinRowsModel
          ![4, 8, 1, 2, 912, 480, 64, 128, 256, 512, 1024, 2048]
          ![0, 0, 4, 8, 0, 0, 832, 512, 256, 0, 0, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1698, 1896, 1508, 1057, 672, 2032, 192, 64, 256, 512, 1024, 2048]
          ![1056, 1696, 1504, 1896, 0, 0, 640, 384, 512, 0, 1024, 0]),
      ((10, false),
        representativeSpinRowsModel
          ![1041, 1752, 1362, 1940, 1072, 16, 128, 192, 256, 512, 1024, 2048]
          ![1040, 1362, 1936, 1752, 0, 32, 128, 0, 512, 0, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![113, 664, 738, 1092, 48, 1040, 1152, 1216, 256, 512, 1024, 2048]
          ![1073, 1696, 4, 1744, 480, 896, 896, 512, 0, 1024, 0, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![355, 1370, 182, 466, 1056, 48, 2032, 336, 256, 512, 1024, 2048]
          ![1072, 1360, 1504, 0, 352, 960, 384, 896, 256, 1536, 1024, 0]),
      ((5, false),
        representativeSpinRowsModel
          ![5, 1092, 1156, 1504, 1342, 1310, 2034, 298, 256, 1838, 302, 2048]
          ![1327, 570, 1476, 792, 448, 608, 1728, 1920, 1280, 0, 1024, 0]),
      ((8, false),
        representativeSpinRowsModel
          ![1941, 480, 852, 1940, 32, 1342, 570, 1000, 256, 1838, 302, 2048]
          ![1326, 298, 724, 0, 1552, 704, 1472, 1408, 256, 1024, 1024, 0]),
      ((13, false),
        representativeSpinRowsModel
          ![556, 933, 332, 624, 564, 214, 570, 1000, 256, 1838, 302, 2048]
          ![286, 1750, 144, 688, 272, 288, 576, 256, 1536, 1536, 0, 0]),
      ((4, false),
        representativeSpinRowsModel
          ![1152, 1362, 1752, 1508, 613, 1648, 857, 720, 1743, 225, 1761, 2048]
          ![285, 370, 1676, 1184, 368, 448, 768, 1536, 0, 1024, 1024, 0]),
      ((6, false),
        representativeSpinRowsModel
          ![1854, 933, 745, 469, 214, 564, 1896, 936, 1975, 409, 1945, 2048]
          ![287, 1198, 1888, 80, 1568, 1088, 192, 256, 1280, 0, 0, 0]),
      ((1, false),
        representativeSpinRowsModel
          ![1582, 1975, 2027, 1239, 1220, 1092, 8, 1706, 933, 1179, 1189, 2048]
          ![286, 254, 880, 1096, 1968, 96, 1152, 128, 256, 1536, 1024, 0]),
      ((9, false),
        representativeSpinRowsModel
          ![12, 1456, 1049, 263, 97, 225, 1197, 527, 933, 1179, 1189, 2048]
          ![819, 300, 1528, 224, 816, 576, 128, 1408, 1024, 1024, 1024, 0]),
      ((0, false),
        representativeSpinRowsModel
          ![738, 794, 310, 1453, 1224, 1065, 523, 4, 963, 1075, 1193, 2919]
          ![300, 76, 180, 680, 48, 704, 0, 0, 1280, 0, 1024, 0]),
      ((12, false),
        representativeSpinRowsModel
          ![310, 1453, 738, 794, 828, 1509, 523, 4, 963, 1075, 1193, 2919]
          ![1752, 1976, 1152, 1360, 544, 192, 512, 512, 1536, 1024, 0, 0])]

/-- Intermediate full spin models, with the exact cocode correction already included. -/
def representativePermutationSpinPlan : Fin 83 → RepresentativeSpinPlan RepresentativeNodeLetter :=
  ![
    representativePermutationSpinPlan960,
    representativePermutationSpinPlan1200,
    representativePermutationSpinPlan1920,
    representativePermutationSpinPlan7722,
    representativePermutationSpinPlan19227,
    representativePermutationSpinPlan22080,
    representativePermutationSpinPlan30720,
    representativePermutationSpinPlan49920,
    representativePermutationSpinPlan130560,
    representativePermutationSpinPlan744960,
    representativePermutationSpinPlan1351680,
    representativePermutationSpinPlan1394880,
    representativePermutationSpinPlan1415040,
    representativePermutationSpinPlan1457280,
    representativePermutationSpinPlan1461120,
    representativePermutationSpinPlan1481280,
    representativePermutationSpinPlan1499520,
    representativePermutationSpinPlan1900800,
    representativePermutationSpinPlan1943040,
    representativePermutationSpinPlan1968000,
    representativePermutationSpinPlan1985280,
    representativePermutationSpinPlan2027520,
    representativePermutationSpinPlan2386560,
    representativePermutationSpinPlan2408640,
    representativePermutationSpinPlan2597760,
    representativePermutationSpinPlan2787840,
    representativePermutationSpinPlan2830080,
    representativePermutationSpinPlan3125760,
    representativePermutationSpinPlan3785280,
    representativePermutationSpinPlan3824640,
    representativePermutationSpinPlan5197440,
    representativePermutationSpinPlan5786880,
    representativePermutationSpinPlan6125760,
    representativePermutationSpinPlan6673920,
    representativePermutationSpinPlan10665600,
    representativePermutationSpinPlan10665792,
    representativePermutationSpinPlan10666560,
    representativePermutationSpinPlan10667712,
    representativePermutationSpinPlan10668768,
    representativePermutationSpinPlan10773794,
    representativePermutationSpinPlan11552640,
    representativePermutationSpinPlan11706825,
    representativePermutationSpinPlan11996160,
    representativePermutationSpinPlan12883200,
    representativePermutationSpinPlan13326720,
    representativePermutationSpinPlan18205440,
    representativePermutationSpinPlan21331776,
    representativePermutationSpinPlan21344741,
    representativePermutationSpinPlan21796800,
    representativePermutationSpinPlan21808524,
    representativePermutationSpinPlan32526135,
    representativePermutationSpinPlan33013198,
    representativePermutationSpinPlan33014936,
    representativePermutationSpinPlan35881849,
    representativePermutationSpinPlan42620160,
    representativePermutationSpinPlan42676038,
    representativePermutationSpinPlan42831984,
    representativePermutationSpinPlan49272960,
    representativePermutationSpinPlan57699840,
    representativePermutationSpinPlan71005440,
    representativePermutationSpinPlan71258152,
    representativePermutationSpinPlan77235657,
    representativePermutationSpinPlan79875840,
    representativePermutationSpinPlan80762880,
    representativePermutationSpinPlan85327112,
    representativePermutationSpinPlan85415649,
    representativePermutationSpinPlan85835153,
    representativePermutationSpinPlan85840916,
    representativePermutationSpinPlan86528640,
    representativePermutationSpinPlan87859296,
    representativePermutationSpinPlan87922499,
    representativePermutationSpinPlan106700773,
    representativePermutationSpinPlan106706497,
    representativePermutationSpinPlan108582478,
    representativePermutationSpinPlan121567626,
    representativePermutationSpinPlan149929934,
    representativePermutationSpinPlan160152960,
    representativePermutationSpinPlan203638538,
    representativePermutationSpinPlan204631599,
    representativePermutationSpinPlan206934638,
    representativePermutationSpinPlan221802288,
    representativePermutationSpinPlan232446768,
    representativePermutationSpinPlan237253688]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
