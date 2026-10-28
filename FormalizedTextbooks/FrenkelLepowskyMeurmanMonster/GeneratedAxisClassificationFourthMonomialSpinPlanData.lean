/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodeSpin

/-! Finite intermediate matrix and phase certificates for the four actual monomial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Convert an original signed source letter to its already verified signed DAG node. -/
def generatedFourthMonomialRepresentativeLetter (l : Fin 2 × Bool) : RepresentativeNodeLetter :=
  (Fin.castAdd 13 l.1, !l.2)

/-- The existing exact full-phase model of the corresponding source letter. -/
def generatedFourthMonomialLetterModel (l : Fin 2 × Bool) : RepresentativeSpinModel :=
  representativeNodeSpinModel (generatedFourthMonomialRepresentativeLetter l)

/-- Full signed spin certificates of the actual original generator letters. -/
theorem generatedFourth_monomial_letter_model (l : Fin 2 × Bool) :
    representativeSpinCertificate (generatedFourthMonomialSpinLetter l)
      (generatedFourthMonomialLetterModel l).coordinate
      (generatedFourthMonomialLetterModel l).phase := by
  have h := representativeNodeSpin_signed_certificate
    (generatedFourthMonomialRepresentativeLetter l)
  have hg : (representativeNodeLetterFiber
      (generatedFourthMonomialRepresentativeLetter l)).val.1 =
        generatedFourthMonomialSpinLetter l := by
    rcases l with ⟨i, b⟩
    fin_cases i <;> cases b
    all_goals
      simp [generatedFourthMonomialRepresentativeLetter, generatedFourthMonomialSpinLetter,
        representativeNodeLetterFiber, representativeNodeFiber,
        representativeNodeFiber0, representativeNodeFiber1, Fin.castAdd, inv_inv]
      rfl
  rw [hg] at h
  exact h

/-- Literal intermediate full-phase models for original monomial word 0. -/
def generatedFourthMonomialSpinPlan0 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
        ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
        ![527, 14, 12, 8, 0, 0, 0, 128, 256, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![12, 523, 4, 5, 581, 113, 536, 209, 269, 512, 1549, 2048]
        ![556, 2, 208, 112, 0, 512, 0, 640, 768, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![241, 1598, 355, 659, 1096, 564, 1756, 713, 271, 1, 1788, 3069]
        ![71, 12, 576, 528, 368, 928, 448, 768, 1792, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![664, 1615, 808, 79, 692, 1660, 1077, 1045, 1362, 1008, 1124, 2971]
        ![1133, 1130, 2008, 0, 512, 1152, 1472, 384, 256, 512, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1698, 1362, 1039, 1896, 425, 1456, 963, 818, 1615, 1239, 1795, 2971]
        ![703, 1258, 1960, 1128, 2016, 1824, 128, 768, 0, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![32, 355, 1598, 745, 8, 1464, 336, 610, 420, 1089, 417, 3083]
        ![1792, 792, 1728, 1584, 1504, 1984, 640, 128, 1536, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![2042, 672, 946, 2035, 393, 1073, 691, 209, 1510, 1771, 385, 2919]
        ![867, 352, 1648, 1888, 848, 1120, 1024, 256, 0, 1536, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![794, 1008, 838, 1453, 2034, 963, 1049, 1224, 1154, 1059, 1659, 2775]
        ![1532, 46, 152, 104, 1136, 64, 1024, 1152, 1280, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![161, 1154, 1935, 356, 128, 113, 1040, 1, 1008, 234, 144, 2775]
        ![1306, 848, 1652, 280, 1792, 1504, 1216, 1536, 512, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1089, 1090, 946, 1096, 16, 241, 145, 1041, 1629, 1771, 1233, 2919]
        ![1748, 1868, 156, 840, 1744, 1184, 1792, 1536, 0, 1024, 0, 0])
  ]

/-- Literal intermediate full-phase models for original monomial word 1. -/
def generatedFourthMonomialSpinPlan1 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
        ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![209, 1218, 1743, 692, 177, 1152, 1056, 97, 828, 332, 1184, 3079]
        ![1085, 1696, 1236, 520, 1312, 1440, 1920, 0, 256, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![624, 828, 912, 2027, 1871, 783, 270, 1342, 1218, 1043, 219, 3079]
        ![513, 1038, 216, 1240, 1200, 1088, 1152, 128, 256, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![512, 1495, 1935, 1838, 1940, 1088, 1509, 1072, 1654, 1147, 731, 2733]
        ![709, 0, 1748, 1544, 800, 1280, 448, 1536, 512, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1, 1752, 4, 8, 1359, 980, 1771, 469, 756, 161, 730, 2048]
        ![1519, 160, 628, 160, 800, 1952, 448, 1024, 512, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![420, 664, 274, 738, 1941, 1691, 783, 1854, 1156, 12, 894, 3069]
        ![1701, 862, 876, 1880, 784, 800, 64, 896, 1280, 0, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1160, 1156, 546, 466, 393, 1207, 1039, 1038, 664, 828, 142, 3069]
        ![185, 924, 1948, 1944, 1664, 352, 576, 1408, 1024, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1073, 4, 1752, 1508, 1423, 312, 1031, 9, 808, 97, 1030, 3840]
        ![1759, 1890, 640, 88, 672, 1312, 1728, 0, 1536, 1024, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1280, 1035, 79, 46, 1464, 1152, 1081, 1072, 1898, 1383, 55, 2397]
        ![41, 1794, 996, 8, 1616, 672, 1408, 384, 512, 0, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1456, 12, 1888, 519, 143, 1039, 1342, 270, 1218, 1043, 1335, 2539]
        ![1585, 60, 1244, 208, 1552, 288, 1664, 384, 0, 1024, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![209, 1218, 1743, 936, 1089, 1088, 16, 161, 12, 1468, 80, 2539]
        ![1085, 594, 980, 1288, 816, 928, 384, 256, 1536, 512, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![97, 1090, 79, 1359, 1041, 1, 241, 177, 523, 1383, 49, 2397]
        ![546, 14, 392, 1488, 880, 0, 704, 256, 1280, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1073, 2, 1752, 1508, 1056, 1040, 128, 64, 1536, 1280, 1024, 3840]
        ![816, 1794, 736, 464, 672, 352, 1600, 1408, 1536, 1536, 1024, 0])
  ]

/-- Literal intermediate full-phase models for original monomial word 2. -/
def generatedFourthMonomialSpinPlan2 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((0, true),
      representativeSpinRowsModel
        ![161, 1154, 1935, 1423, 1041, 1073, 1217, 1089, 1239, 1147, 1025, 2733]
        ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![172, 1239, 2007, 1495, 1092, 1077, 1224, 1049, 1154, 1059, 1537, 2733]
        ![527, 14, 12, 8, 0, 0, 0, 128, 256, 1024, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![128, 1743, 1218, 225, 745, 1756, 1660, 613, 312, 788, 1709, 3086]
        ![1027, 1198, 1812, 1336, 560, 1440, 192, 640, 512, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1081, 519, 1160, 1948, 1220, 536, 564, 81, 720, 586, 1581, 3840]
        ![785, 964, 1960, 744, 496, 288, 0, 384, 1792, 1536, 0, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![154, 720, 252, 1000, 1043, 1754, 597, 1061, 519, 1598, 1337, 3840]
        ![312, 1696, 1676, 640, 1024, 1056, 0, 0, 1280, 0, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1059, 1466, 1218, 1090, 298, 713, 284, 1648, 1435, 788, 282, 3086]
        ![1343, 732, 660, 1360, 880, 896, 192, 128, 1280, 0, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1679, 1435, 1615, 1743, 267, 1310, 1127, 1277, 1466, 409, 410, 3086]
        ![1099, 424, 44, 488, 1392, 224, 1024, 1408, 256, 512, 1024, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1900, 252, 720, 841, 1566, 768, 1935, 882, 1360, 1075, 1813, 2683]
        ![1568, 1536, 1756, 728, 1712, 1568, 512, 1024, 1024, 0, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![355, 1360, 371, 234, 946, 1359, 1999, 209, 252, 1936, 1676, 2683]
        ![338, 574, 1064, 1376, 1504, 192, 1152, 1152, 0, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![128, 1090, 1615, 192, 1342, 1789, 1629, 1822, 949, 409, 1548, 3086]
        ![1198, 1036, 836, 456, 48, 1536, 640, 896, 512, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![512, 269, 2007, 1915, 818, 963, 274, 323, 1582, 1679, 1036, 2733]
        ![1165, 12, 124, 216, 512, 416, 576, 384, 256, 1024, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![161, 1582, 597, 761, 1041, 1073, 1089, 1217, 269, 781, 1184, 2733]
        ![1548, 0, 1184, 1184, 176, 96, 128, 0, 256, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1, 527, 2034, 1362, 177, 32, 97, 128, 1654, 172, 1185, 2048]
        ![1667, 14, 1660, 1744, 160, 736, 192, 640, 512, 0, 1024, 0])
  ]

/-- Literal intermediate full-phase models for original monomial word 3. -/
def generatedFourthMonomialSpinPlan3 : RepresentativeSpinPlan (Fin 2 × Bool) :=
  [
    ((1, true),
      representativeSpinRowsModel
        ![768, 256, 519, 523, 274, 323, 546, 643, 2, 3, 1036, 2048]
        ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![192, 1935, 1154, 1153, 1566, 1885, 1965, 1326, 1464, 1652, 1804, 2255]
        ![1855, 1276, 688, 368, 512, 256, 768, 768, 512, 0, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![691, 1453, 1698, 214, 466, 1679, 1359, 97, 92, 556, 1996, 3083]
        ![1628, 1838, 1220, 368, 1600, 1408, 1984, 256, 512, 1024, 1024, 0]),
    ((1, true),
      representativeSpinRowsModel
        ![624, 92, 912, 1508, 1059, 525, 270, 1363, 1453, 1822, 440, 3083]
        ![1072, 2032, 968, 1984, 1488, 1728, 1280, 640, 1024, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![1326, 1207, 512, 1310, 2027, 1510, 1941, 710, 122, 336, 968, 2127]
        ![350, 1074, 656, 632, 640, 1568, 768, 768, 256, 512, 0, 0]),
    ((0, true),
      representativeSpinRowsModel
        ![526, 1465, 1699, 2035, 269, 1259, 949, 371, 745, 727, 1766, 3087]
        ![878, 0, 2036, 1808, 544, 800, 128, 512, 1280, 0, 0, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![62, 745, 963, 659, 1629, 1771, 901, 1043, 1465, 1975, 1974, 3087]
        ![879, 1890, 452, 576, 1472, 1728, 1216, 128, 1536, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1822, 1495, 512, 1838, 491, 182, 933, 1942, 586, 336, 168, 2127]
        ![351, 848, 1184, 1832, 1552, 672, 1280, 384, 256, 1024, 1024, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![624, 828, 912, 1508, 323, 349, 1854, 1075, 1789, 1326, 728, 3083]
        ![1537, 162, 1704, 672, 1664, 960, 1088, 512, 0, 512, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![979, 1789, 2034, 390, 1154, 143, 1871, 81, 828, 332, 1196, 3083]
        ![1805, 796, 932, 1392, 400, 288, 1984, 896, 512, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![192, 1423, 466, 177, 46, 1037, 1277, 1822, 1752, 1652, 1132, 2255]
        ![830, 1278, 1488, 1392, 848, 1440, 384, 128, 1024, 1536, 0, 0]),
    ((0, false),
      representativeSpinRowsModel
        ![1792, 1280, 871, 1035, 1090, 1059, 882, 995, 1362, 355, 876, 3584]
        ![621, 1230, 8, 0, 1360, 1760, 1728, 640, 1280, 1536, 1024, 0]),
    ((1, false),
      representativeSpinRowsModel
        ![1073, 1362, 4, 1896, 1040, 1056, 64, 128, 1280, 512, 1024, 3584]
        ![561, 850, 1536, 352, 496, 928, 1856, 640, 512, 1536, 1024, 0])
  ]

/-- The four original word plans, with every finite intermediate phase retained. -/
def generatedFourthMonomialSpinPlan : Fin 4 → RepresentativeSpinPlan (Fin 2 × Bool) :=
  ![generatedFourthMonomialSpinPlan0, generatedFourthMonomialSpinPlan1,
    generatedFourthMonomialSpinPlan2, generatedFourthMonomialSpinPlan3]

/-- Literal plans describe precisely the four original actual source words. -/
theorem generatedFourth_monomial_plan_letters : ∀ k : Fin 4,
    (generatedFourthMonomialSpinPlan k).map Prod.fst = generatedFourthMonomialWord k := by
  decide +kernel

/-- The final explicit full matrix and phase model of each original monomial word. -/
def generatedFourthMonomialSpinModel (k : Fin 4) : RepresentativeSpinModel :=
  representativeSpinPlanEnd representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
