/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSyndromeMasks

/-! The literal odd theta cache is checked against every original Parker vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
/-- Theta labels for the completely bound 512 original odd-code families. -/
def generatedSixthXiOddThetaLabels : Fin 512 → Fin 4096 :=
  ![0, 14, 13, 1027, 11, 1029, 1030, 1032, 7, 1033, 1034, 1028,
    1036, 1026, 1025, 15, 779, 789, 246, 1256, 768, 1822, 1277, 1251,
    108, 1138, 1937, 1935, 1127, 1145, 1946, 900, 523, 565, 166, 1176,
    512, 1598, 1197, 1171, 220, 1250, 1649, 1615, 1239, 1257, 1658, 580,
    267, 293, 86, 1144, 256, 1326, 1117, 1139, 188, 1170, 1505, 1487,
    1207, 1177, 1514, 452, 1092, 1658, 1817, 295, 1615, 113, 274, 812,
    1315, 797, 638, 64, 808, 278, 117, 1611, 1708, 1154, 1537, 47,
    1191, 649, 10, 548, 1195, 645, 6, 552, 672, 142, 525, 1059,
    1077, 1595, 1480, 966, 1598, 48, 963, 461, 1922, 396, 639, 113,
    393, 903, 116, 1658, 1750, 1224, 1243, 709, 1245, 707, 720, 206,
    1537, 31, 12, 530, 10, 532, 519, 1049, 1220, 1514, 1593, 791,
    1487, 225, 818, 540, 1811, 573, 494, 192, 536, 822, 229, 1483,
    1462, 1160, 1211, 389, 1213, 387, 432, 142, 1281, 63, 12, 306,
    10, 308, 263, 1081, 1372, 1090, 1281, 31, 1111, 329, 10, 276,
    1115, 325, 6, 280, 336, 78, 269, 1043, 1061, 1323, 1928, 646,
    1326, 32, 643, 909, 1602, 844, 495, 225, 841, 583, 228, 1514,
    1156, 1946, 1321, 567, 1935, 145, 546, 316, 1587, 301, 926, 128,
    312, 550, 149, 1931, 1045, 1819, 1608, 326, 1822, 16, 323, 589,
    1474, 716, 927, 145, 713, 455, 148, 1946, 1894, 1096, 1131, 837,
    1133, 835, 864, 78, 1793, 47, 12, 802, 10, 804, 775, 1065,
    2044, 1218, 1793, 63, 1271, 969, 10, 820, 1275, 965, 6, 824,
    1008, 206, 781, 1075, 15, 31, 351, 1359, 927, 1935, 1743, 1759,
    735, 1743, 1935, 1951, 1359, 1375, 1055, 15, 14, 14, 686, 1710,
    926, 1950, 1342, 1342, 446, 1470, 1822, 1822, 1582, 1582, 1166, 142,
    775, 807, 247, 1239, 151, 1207, 1895, 1863, 775, 1831, 1271, 1239,
    1175, 1207, 1895, 839, 781, 829, 781, 1853, 157, 1197, 1181, 1197,
    109, 1117, 1133, 1117, 2045, 1997, 2045, 973, 1666, 1186, 1154, 674,
    1810, 306, 274, 818, 1330, 786, 818, 274, 162, 642, 674, 1154,
    1888, 1360, 1680, 160, 1776, 192, 768, 304, 1968, 384, 576, 112,
    544, 16, 976, 1504, 2032, 1504, 1872, 320, 1632, 112, 704, 208,
    1680, 128, 560, 32, 768, 272, 928, 1456, 1561, 1049, 1353, 841,
    1929, 393, 217, 729, 1049, 537, 841, 329, 393, 905, 729, 1241,
    1416, 1208, 1576, 792, 1816, 552, 184, 392, 1160, 440, 808, 536,
    536, 808, 440, 1160, 2032, 1744, 1952, 640, 1376, 64, 304, 16,
    1424, 176, 448, 224, 768, 544, 848, 1648, 1299, 1043, 1043, 275,
    1923, 643, 643, 899, 1731, 963, 963, 707, 83, 339, 339, 1107,
    1888, 1648, 1424, 128, 1520, 224, 768, 528, 2000, 704, 288, 48,
    320, 80, 944, 1696, 1793, 1025, 2033, 241, 1937, 145, 865, 97,
    1889, 97, 913, 145, 1009, 241, 769, 1025, 1178, 1930, 1946, 138,
    1034, 794, 778, 26, 1946, 138, 154, 906, 778, 26, 10, 1818,
    1504, 1744, 1968, 128, 1392, 576, 800, 16, 1872, 96, 256, 560,
    960, 240, 400, 1696, 1648, 1360, 2000, 240, 1760, 448, 832, 96,
    1952, 128, 512, 288, 816, 16, 656, 1456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check all 512 original Parker theta vectors; discovered labels are not assumed.
/-- Every displayed odd theta label is the actual original preferred-lift vector. -/
theorem generatedSixth_xi_odd_theta_cache : ∀ f : Fin 512,
    sourceWordTheta ⟨(generatedSixthMonomialOddCode f).val, by omega⟩ =
      golayLabelCoefficients (generatedSixthXiOddThetaLabels f) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
