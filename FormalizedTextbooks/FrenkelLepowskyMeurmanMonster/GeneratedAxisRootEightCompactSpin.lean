/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactData

/-! Actual compact spin factors for the original root-eight words and incoming transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactLeftColumns : Fin 14 → Fin 12 → ℕ :=
  ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![3883, 2353, 2386, 2328, 3977, 3934, 1, 2, 4, 8, 256, 512],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![2092, 32, 3942, 2058, 2111, 10, 15, 2732, 1, 64, 128, 256],
    ![1985, 2359, 37, 16, 198, 3781, 2366, 437, 1, 2, 64, 512]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactLeftInverseColumns : Fin 14 → Fin 12 → ℕ :=
  ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![64, 128, 256, 512, 423, 586, 652, 731, 1024, 2048, 2852, 1967],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![256, 363, 352, 331, 122, 2, 512, 1024, 2048, 1153, 3748, 40],
    ![256, 512, 559, 322, 8, 811, 1024, 1087, 1203, 2048, 3469, 1725]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactRightColumns : Fin 14 → Fin 12 → ℕ :=
  ![![1968, 1872, 1835, 8, 1807, 1855, 222, 2018, 304, 1327, 972, 2048],
    ![1, 1712, 1591, 1654, 1775, 1548, 13, 128, 1970, 589, 556, 2048],
    ![1968, 1952, 1942, 1929, 3, 51, 2018, 222, 1713, 1426, 972, 2048],
    ![1968, 2, 1861, 1815, 1953, 109, 1967, 147, 350, 1292, 780, 2048],
    ![4, 2044, 1861, 1835, 16, 128, 208, 176, 1652, 1508, 1024, 2048],
    ![1, 2, 15, 4, 123, 150, 128, 193, 459, 589, 1153, 2048],
    ![8, 2, 15, 1, 185, 222, 235, 126, 350, 672, 1186, 2048],
    ![8, 2, 1, 4, 63, 16, 150, 229, 291, 565, 1055, 2048],
    ![2, 1, 8, 4, 16, 32, 80, 160, 272, 544, 1024, 2048],
    ![1, 4, 8, 2, 48, 16, 128, 192, 256, 512, 1024, 2048],
    ![1152, 1920, 64, 1923, 576, 588, 896, 16, 32, 3264, 2693, 1921],
    ![481, 258, 260, 8, 1704, 448, 2040, 1752, 256, 2824, 3080, 2048],
    ![3072, 3075, 4, 3073, 1280, 2560, 2576, 3896, 2816, 1048, 64, 128],
    ![768, 1792, 256, 268, 1558, 2560, 833, 3110, 1542, 2337, 1794, 128]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactRightInverseColumns : Fin 14 → Fin 12 → ℕ :=
  ![![1968, 1872, 1835, 8, 1807, 1855, 222, 2018, 304, 1327, 972, 2048],
    ![1, 1712, 1591, 1654, 1775, 1548, 13, 128, 1970, 589, 556, 2048],
    ![1968, 1952, 1942, 1929, 3, 51, 2018, 222, 1713, 1426, 972, 2048],
    ![1968, 2, 1861, 1815, 1953, 109, 1967, 147, 350, 1292, 780, 2048],
    ![1861, 1806, 1, 1987, 16, 176, 112, 32, 1761, 1489, 1024, 2048],
    ![1, 2, 8, 15, 106, 183, 193, 64, 397, 711, 1089, 2048],
    ![8, 2, 15, 1, 185, 222, 235, 126, 350, 672, 1186, 2048],
    ![4, 2, 8, 1, 32, 63, 217, 106, 313, 531, 1071, 2048],
    ![2, 1, 8, 4, 16, 32, 80, 160, 272, 544, 1024, 2048],
    ![1, 8, 2, 4, 32, 48, 192, 64, 256, 512, 1024, 2048],
    ![2050, 2056, 3664, 3680, 128, 256, 4, 67, 23, 20, 66, 517],
    ![481, 258, 260, 8, 1704, 448, 2040, 1752, 256, 2824, 3080, 2048],
    ![9, 10, 4, 848, 96, 896, 1024, 2048, 288, 273, 304, 305],
    ![897, 1026, 1284, 1288, 272, 416, 960, 2048, 4, 5, 3, 37]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactFirstPhaseRows : Fin 14 → Fin 12 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4094, 3540, 1680, 160, 3488, 3072, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1808, 2816, 2072, 128, 3584, 640, 3712, 256, 0, 0, 0, 0],
    ![2826, 2520, 2144, 1616, 576, 3648, 1024, 2304, 0, 0, 0, 0]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactSecondPhaseRows : Fin 14 → Fin 12 → ℕ :=
  ![![1704, 172, 440, 1712, 128, 64, 512, 512, 1024, 0, 0, 0],
    ![286, 1936, 1768, 736, 640, 64, 0, 256, 1536, 1024, 0, 0],
    ![1890, 160, 984, 2000, 128, 832, 512, 256, 1024, 0, 0, 0],
    ![1162, 252, 1296, 1344, 1056, 1280, 1152, 1280, 0, 0, 0, 0],
    ![624, 0, 0, 912, 768, 512, 256, 768, 512, 0, 0, 0],
    ![0, 1360, 1648, 1888, 800, 512, 0, 0, 512, 0, 0, 0],
    ![1040, 0, 1504, 1456, 160, 64, 128, 0, 1536, 0, 0, 0],
    ![1056, 1696, 1504, 1888, 0, 0, 384, 768, 512, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 512, 256, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 3712, 3312, 1344, 2080, 2176, 3968, 768, 1024, 1024, 2048, 0],
    ![534, 672, 624, 0, 320, 704, 768, 256, 0, 0, 0, 0],
    ![3368, 3328, 552, 1808, 1824, 2816, 2176, 512, 2048, 2048, 2048, 0],
    ![3096, 524, 2488, 624, 1888, 1536, 256, 256, 0, 2048, 2048, 0]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactBinaryColumns : Fin 14 → Fin 24 → ℕ :=
  ![![7440304, 7767888, 5474091, 7041032, 5035791, 4253503, 7413982, 5343202, 5009712, 4502831,
    4191180, 2048, 2310144, 3096576, 6750208, 6799360, 1454080, 3821568, 4988928, 4984832, 8089600,
    4943872, 2846720, 8388608],
    ![1171457, 6067888, 4920887, 5781110, 6182639, 2180620, 5316621, 1171584, 5093298, 131661,
    1434156, 2048, 2445312, 1163264, 6799360, 6750208, 1105920, 5365760, 2195456, 1646592, 1048576,
    7593984, 1302528, 8388608],
    ![7440304, 7948192, 7481238, 4593545, 8138755, 4243507, 5343202, 7413982, 5076657, 4814226,
    4191180, 2048, 1277952, 3096576, 4734976, 4751360, 3821568, 1454080, 4980736, 8187904, 6615040,
    5566464, 3469312, 8388608],
    ![4351920, 1036290, 5519173, 5318423, 4761505, 5517421, 4351919, 5316755, 704862, 1292,
    1037068, 2048, 1032192, 1875968, 7782400, 7733248, 1609728, 462848, 1196032, 856064, 7720960,
    4575232, 2478080, 8388608],
    ![4, 4130812, 67397, 526123, 3182608, 3178624, 1048784, 2097328, 1771124, 2950628, 1024, 2048,
    3198976, 40960, 12288, 8192, 2555904, 1966080, 3444736, 3309568, 2142208, 1093632, 7385088,
    8388608],
    ![1, 5570562, 4456463, 6750212, 3162235, 24726, 128, 57537, 147915, 139853, 58497, 2048,
    7770112, 2334720, 3309568, 1163264, 131072, 196608, 7143424, 3538944, 1048576, 2097152,
    4194304, 8388608],
    ![5963784, 2, 4456463, 4259841, 1085625, 4318, 1065195, 4222, 6623582, 1049248, 1103010, 2048,
    376832, 6184960, 1720320, 2052096, 1769472, 7143424, 1966080, 6750208, 1048576, 2097152,
    4194304, 8388608],
    ![7733256, 6946818, 4325377, 6160388, 61503, 16, 24726, 3166437, 274723, 283189, 62495, 2048,
    7766016, 6955008, 4329472, 6176768, 3538944, 5963776, 786432, 262144, 1048576, 2097152,
    4194304, 8388608],
    ![2, 1, 8, 4, 16, 32, 2097232, 1048736, 524560, 262688, 1024, 2048, 8192, 4096, 32768, 16384,
    1376256, 2752512, 262144, 524288, 1048576, 2097152, 4194304, 8388608],
    ![1, 4, 8, 2, 48, 16, 128, 192, 256, 512, 1024, 2048, 4096, 16384, 32768, 8192, 131072, 196608,
    786432, 262144, 1048576, 2097152, 4194304, 8388608],
    ![1386308, 6584161, 7102539, 5656955, 12921202, 15149477, 14769946, 5154316, 5236443, 4646331,
    9096532, 2035280, 2908160, 11378475, 6672384, 15890737, 14051666, 12921112, 106570, 12218249,
    16715614, 8159306, 1867850, 10421840],
    ![2187745, 2560258, 2756868, 8, 3684008, 2908608, 1189880, 3360472, 852224, 752392, 3080, 2048,
    4096, 8192, 16384, 7176192, 786432, 331776, 921600, 987136, 3567616, 2949120, 5046272,
    14680064],
    ![1790384, 3955120, 2048, 461232, 4669579, 5631164, 8131772, 4428855, 6767758, 1097676,
    1063596, 3670031, 3799084, 1372192, 13676390, 3737612, 6031370, 2381887, 3973173, 2359306,
    7927808, 264192, 1835023, 4315820],
    ![15535951, 538317, 4651113, 9897750, 1636367, 3973826, 13197135, 7846449, 2160640, 8981928,
    7091960, 6836261, 5183425, 10950967, 5910565, 417808, 5464262, 9875141, 13076798, 4214842,
    15700169, 11992831, 8894722, 3690933]]

/-- Exact full original binary coefficients for the compact spin factors. -/
def generatedRootEightCompactUnitPhases : Fin 14 → Fin 24 → ℕ :=
  ![![0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1]]

/-- The number of original individual Fourier factors in each actual compact model. -/
def generatedRootEightCompactHadamardRank : Fin 14 → Fin 13 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 8, 8]

/-- The actual full Pauli coordinates, with a chosen zero scalar representative. -/
def generatedRootEightCompactPauliLabels : Fin 14 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(0, 96, 0), (0, 381, 0), (0, 851, 0), (0, 1595, 0), (0, 467, 0), (0, 1973, 0), (0, 238, 0), (0,
    1751, 0), (0, 1029, 0), (0, 1167, 0), (3925, 2361, 0), (2048, 929, 0), (2493, 1426, 0), (3601,
    464, 0)]

set_option maxHeartbeats 8000000 in
-- Evaluate the two-sided binary matrix products for both original monomial factors.
/-- Every compact monomial factor has its actual two-sided binary inverse. -/
theorem generatedRootEight_compact_matrix_inverse : ∀ i : Fin 14,
    (generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactLeftInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactLeftColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactLeftColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactLeftInverseColumns i) = 1) ∧
    (generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactRightInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactRightColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactRightColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedRootEightCompactRightInverseColumns i) = 1)
    := by
  decide +kernel

/-- The left original compact monomial is a genuine binary spin equivalence. -/
def generatedRootEightCompactLeft (i : Fin 14) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedRootEightCompactLeftColumns i)
    (generatedRootEightCompactLeftInverseColumns i)
    (generatedRootEight_compact_matrix_inverse i).1.1
    (generatedRootEight_compact_matrix_inverse i).1.2

/-- The right original compact monomial is a genuine binary spin equivalence. -/
def generatedRootEightCompactRight (i : Fin 14) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedNinthLowerSpinCompactEquiv (generatedRootEightCompactRightColumns i)
    (generatedRootEightCompactRightInverseColumns i)
    (generatedRootEight_compact_matrix_inverse i).2.1
    (generatedRootEight_compact_matrix_inverse i).2.2

/-- The full Pauli factor belongs to the actual original extraspecial group. -/
def generatedRootEightCompactPauli (i : Fin 14) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedRootEightCompactPauliLabels i).1)
    (golayLabelCoefficients (generatedRootEightCompactPauliLabels i).2.1)),
    ofAdd (generatedRootEightCompactPauliLabels i).2.2⟩

/-- The prescribed original coordinates receive the individual Fourier factors. -/
def generatedRootEightCompactHadamardWord (i : Fin 14) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => k.val < (generatedRootEightCompactHadamardRank i).val)

/-- An actual orthogonal spin normalizer built from original monomials, phases and Fourier maps. -/
def generatedRootEightCompactSpin (i : Fin 14) : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedRootEightCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows i)) *
    ((generatedRootEightCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedRootEightCompactRight i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
