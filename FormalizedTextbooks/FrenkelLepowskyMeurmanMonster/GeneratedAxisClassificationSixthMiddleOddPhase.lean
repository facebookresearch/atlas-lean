/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddData

/-! Complete preferred central phases for the 276 genuine middle odd-short images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Literal modulation labels of the displayed genuine physical source pairs. -/
def generatedSixthMiddleOddModulation : Fin 276 → Fin 4096 :=
  ![1536, 1280, 1792, 1039, 143, 79, 207, 1038, 46, 30, 62, 1037,
    685, 349, 1021, 1035, 491, 923, 635, 1031, 871, 727, 439, 768,
    256, 527, 1679, 1615, 1743, 526, 1582, 1566, 1598, 525, 1197, 1885,
    1533, 523, 2027, 1435, 1147, 519, 1383, 1239, 1975, 512, 271, 1423,
    1359, 1487, 270, 1326, 1310, 1342, 269, 1965, 1117, 1789, 267, 1259,
    1691, 1915, 263, 1639, 2007, 1207, 783, 1935, 1871, 1999, 782, 1838,
    1822, 1854, 781, 1453, 1629, 1277, 779, 1771, 1179, 1403, 775, 1127,
    1495, 1719, 1152, 1088, 1216, 1, 1057, 1041, 1073, 2, 1698, 1362,
    2034, 4, 1508, 1940, 1652, 8, 1896, 1752, 1464, 192, 64, 1153,
    161, 145, 177, 1154, 546, 466, 882, 1156, 356, 788, 756, 1160,
    1000, 600, 312, 128, 1089, 97, 81, 113, 1090, 738, 274, 946,
    1092, 420, 980, 564, 1096, 808, 664, 504, 1217, 225, 209, 241,
    1218, 610, 402, 818, 1220, 292, 852, 692, 1224, 936, 536, 376,
    1056, 1040, 1072, 3, 1699, 1363, 2035, 5, 1509, 1941, 1653, 9,
    1897, 1753, 1465, 48, 16, 1059, 643, 371, 979, 1061, 453, 949,
    597, 1065, 841, 761, 409, 32, 1043, 691, 323, 995, 1045, 501,
    901, 613, 1049, 889, 713, 425, 1075, 659, 355, 963, 1077, 469,
    933, 581, 1081, 857, 745, 393, 1696, 1360, 2032, 6, 1510, 1942,
    1654, 10, 1898, 1754, 1466, 1008, 336, 1702, 838, 310, 214, 1706,
    458, 122, 794, 672, 1366, 182, 710, 806, 1370, 570, 906, 234,
    2038, 534, 102, 390, 2042, 154, 298, 586, 1504, 1936, 1648, 12,
    1900, 1756, 1468, 624, 912, 1516, 652, 828, 92, 480, 1948, 252,
    332, 556, 1660, 284, 172, 972, 1888, 1744, 1456, 432, 720, 864]

/-- Cached preferred-Q central phase bits, checked against the full actual word image. -/
def generatedSixthMiddleOddPreferredPhase : Fin 276 → ZMod 2 :=
  ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1,
    0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1,
    1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0]

/-- The finite source modulation labels are exactly the genuine pair syndromes. -/
theorem generatedSixth_middle_odd_syndrome (k : Fin 276) :
    griessPairSyndrome (generatedSixthMiddleOddInput k).2 =
      golayLabelCoefficients (generatedSixthMiddleOddModulation k) := by
  unfold griessPairSyndrome generatedSixthMiddleOddInput
  rw [griessPairIndex_coordinates, ite_eq_left (generatedSixth_middle_odd_source_lt k)]
  revert k
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check 276 central bits using the twelve proved original basis images and frame translation.
/-- Every cached phase is the central coefficient of the actual original full Q image. -/
theorem generatedSixth_middle_odd_phase_certificate (k : Fin 276) :
    Multiplicative.toAdd (generatedSixthPairQImage
      (generatedSixthMiddleOddSourceCoordinates k).1
      (golayLabelCoefficients (generatedSixthMiddleOddModulation k))).coeff =
        generatedSixthMiddleOddPreferredPhase k := by
  revert k
  decide +kernel

/-- The cached bits are the genuine local-short phases of the original source word. -/
theorem generatedSixth_middle_odd_phase (k : Fin 276) :
    generatedSixthMiddleShortPhase (generatedSixthMiddleOddInput k) =
      generatedSixthMiddleOddPreferredPhase k := by
  rw [generatedSixth_pair_Q_phase, generatedSixth_middle_odd_syndrome]
  exact generatedSixth_middle_odd_phase_certificate k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
