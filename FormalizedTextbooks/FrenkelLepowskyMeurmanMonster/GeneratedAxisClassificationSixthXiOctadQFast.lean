/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates

/-! Original Parker theta values accelerate the actual preferred octad-Q source evaluation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Literal theta labels for the genuine 231 original octad families. -/
def generatedSixthXiOctadThetaLabels : Fin 231 → Fin 4096 :=
  ![1028, 1392, 1760, 792, 1181, 1632, 913, 1376, 1175, 10, 905, 1030,
    786, 1776, 1950, 1951, 1029, 1036, 899, 11, 1520, 1696, 1456, 1160,
    1997, 1456, 1025, 1648, 1863, 794, 217, 1026, 1154, 1504, 1166, 15,
    1025, 1032, 83, 15, 1696, 779, 461, 1608, 1220, 1658, 1750, 1587,
    1505, 63, 1968, 78, 1061, 1218, 1065, 1744, 1872, 295, 1504, 1708,
    206, 1321, 1462, 1514, 1077, 1474, 1649, 573, 2000, 583, 1372, 1096,
    1075, 1360, 1952, 47, 1648, 1092, 32, 78, 797, 1251, 1043, 142,
    781, 552, 926, 589, 432, 1811, 184, 1160, 512, 392, 1139, 1537,
    1008, 1281, 1937, 1793, 64, 781, 1049, 1480, 1176, 1177, 1853, 1133,
    1160, 781, 1593, 269, 2044, 1315, 495, 1138, 1872, 1257, 267, 1224,
    1658, 1504, 1680, 567, 2032, 1045, 525, 864, 768, 909, 1009, 791,
    263, 1946, 1946, 1025, 865, 903, 769, 519, 1602, 638, 47, 1952,
    455, 1156, 1514, 1081, 1744, 1424, 1144, 2032, 523, 1793, 1154, 1271,
    48, 1537, 1170, 1171, 1831, 775, 192, 775, 1281, 31, 1946, 142,
    494, 128, 16, 906, 1946, 31, 154, 639, 329, 256, 1250, 1922,
    720, 1049, 1049, 927, 537, 301, 1154, 1680, 1710, 1375, 1027, 1034,
    1043, 13, 1424, 1145, 672, 1817, 162, 306, 775, 642, 206, 1658,
    1059, 1360, 1968, 63, 1888, 1894, 1946, 14, 1470, 1928, 14, 1090,
    1055, 1759, 336, 15, 1514, 1033, 1043, 14, 1648, 707, 7, 2000,
    275, 1256, 1888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Check all 231 original Parker theta vectors without assuming their discovered labels.
/-- Every theta label is the actual original preferred-lift theta vector. -/
theorem generatedSixth_xi_octad_theta_cache : ∀ f : Fin 231,
    sourceWordTheta (generatedSixthFinalOctadCacheCode f) =
      golayLabelCoefficients (generatedSixthXiOctadThetaLabels f) := by
  decide +kernel

/-- Complete finite preferred source-Q lift, with cached theta and genuine negative positions. -/
def generatedSixthXiOctadQFast (f : Fin 231) (e : Fin 64) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f) +
      griessOctadOmegaCoefficient e • Pi.single 11 1)
    (golayLabelCoefficients (generatedSixthXiOctadThetaLabels f) +
      golaySyndrome (integerParity (generatedSixthMonomialOctadNegativeInteger f e)))), 1⟩

/-- Cached evaluation equals every coordinate and central bit of the genuine preferred Q lift. -/
theorem generatedSixth_xi_octad_Q_fast (f : Fin 231) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
      generatedSixthXiOctadQFast f e := by
  have hn : griessOctadNegativeInteger (generatedSixthFinalOctadCacheOctad f) e =
      generatedSixthMonomialOctadNegativeInteger f e := by
    funext i
    exact generatedSixth_monomial_octad_negative_integer f e i
  rw [← monsterNortonShortQSource_actual]
  simp only [monsterNortonShortQSource, monsterNortonShortTranslation,
    monsterNortonShortModulation]
  rw [hn, generatedSixth_final_octad_cache_label, generatedSixth_xi_octad_theta_cache]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
