/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinHadamard
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData

/-! Exact compact integer data and two-sided binary matrix inverse certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactLeftColumns : Fin 11 → Fin 12 → ℕ :=
  ![
    ![2048, 3, 1, 4, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![2048, 971, 1, 2, 4, 8, 16, 32, 64, 128, 256, 1024],
    ![2048, 1899, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512],
    ![2048, 1931, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512],
    ![446, 1749, 907, 3797, 2001, 8, 1, 2, 4, 16, 32, 64],
    ![3724, 971, 2535, 1928, 1, 2, 4, 8, 16, 32, 64, 256],
    ![1572, 644, 875, 3684, 669, 1292, 1842, 3033, 1, 2, 4, 32],
    ![1302, 1757, 875, 1366, 3780, 3646, 3890, 235, 1, 2, 4, 32],
    ![3780, 2660, 875, 1668, 1302, 2695, 2137, 825, 1, 4, 8, 32],
    ![3286, 1611, 2816, 957, 82, 1958, 2832, 1684, 1682, 3604, 1, 2],
    ![902, 2387, 2335, 2061, 2961, 2505, 2564, 1650, 2957, 3473, 2, 8]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactLeftInverseColumns : Fin 11 → Fin 12 → ℕ :=
  ![
    ![4, 6, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 1],
    ![4, 8, 16, 32, 64, 128, 256, 512, 1024, 1838, 2048, 1],
    ![4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 3502, 1],
    ![4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 3630, 1],
    ![64, 128, 256, 32, 512, 1024, 2048, 1715, 274, 1861, 2740, 10],
    ![16, 32, 64, 128, 256, 512, 1024, 1597, 2048, 2703, 1082, 2121],
    ![256, 512, 1024, 970, 728, 2048, 805, 2928, 1177, 3954, 883, 812],
    ![256, 512, 1024, 910, 432, 2048, 9, 2055, 2030, 3949, 95, 812],
    ![256, 375, 512, 1024, 1353, 2048, 1210, 3311, 706, 2571, 1260, 1203],
    ![1024, 2048, 2432, 1917, 68, 2101, 2132, 2671, 209, 2106, 2833, 2287],
    ![366, 1024, 1289, 2048, 3097, 1926, 3343, 59, 2069, 2342, 2870, 3183]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactRightColumns : Fin 11 → Fin 12 → ℕ :=
  ![
    ![1128, 1129, 8, 1288, 3972, 64, 128, 4048, 512, 4040, 1744, 2],
    ![2948, 2952, 1280, 32, 3008, 2560, 256, 2176, 272, 2237, 2048, 2],
    ![4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 3501, 2],
    ![3496, 3620, 1768, 3596, 64, 768, 256, 384, 760, 212, 3629, 2],
    ![64, 128, 256, 8, 512, 1024, 2048, 1682, 260, 1877, 2690, 32],
    ![1184, 1168, 3248, 128, 3568, 512, 1024, 1593, 1264, 1660, 1073, 2114],
    ![256, 512, 1024, 779, 514, 2048, 803, 2899, 1028, 3863, 899, 771],
    ![256, 512, 1024, 779, 257, 2048, 32, 2128, 1799, 3863, 128, 771],
    ![256, 259, 512, 1024, 1289, 2048, 1064, 3160, 516, 2580, 1160, 1032],
    ![1024, 2048, 3079, 3083, 16, 32, 2114, 128, 1281, 3075, 2050, 512],
    ![1, 2048, 4, 3072, 3096, 32, 3080, 1098, 128, 256, 1034, 512]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactRightInverseColumns : Fin 11 → Fin 12 → ℕ :=
  ![
    ![3, 2048, 564, 4, 644, 1985, 32, 64, 2024, 256, 2020, 872],
    ![971, 2048, 1249, 1250, 320, 8, 1264, 1152, 64, 1056, 68, 1024],
    ![1899, 2048, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512],
    ![1931, 2048, 874, 905, 442, 899, 16, 192, 64, 96, 190, 53],
    ![2001, 1106, 260, 8, 1248, 2048, 1, 2, 4, 16, 32, 64],
    ![1091, 2308, 1928, 1184, 74, 73, 331, 8, 351, 32, 64, 79],
    ![2065, 18, 260, 2056, 2848, 2112, 896, 3072, 1, 2, 4, 32],
    ![17, 2066, 2308, 2056, 800, 64, 896, 1024, 1, 2, 4, 32],
    ![2065, 2066, 260, 2056, 800, 2112, 2944, 3072, 1, 4, 8, 32],
    ![1537, 1026, 516, 520, 16, 32, 1088, 128, 1792, 2048, 1, 2],
    ![1, 1090, 4, 72, 80, 32, 1152, 256, 512, 2048, 10, 2]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactFirstPhaseRows : Fin 11 → Fin 12 → ℕ :=
  ![
    ![2118, 2052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1086, 1216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 3624, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![42, 2596, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![224, 404, 1432, 1360, 448, 448, 0, 0, 0, 0, 0, 0],
    ![2544, 2820, 2072, 3040, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2922, 660, 1328, 240, 1184, 3648, 3072, 1024, 0, 0, 0, 0],
    ![1078, 2280, 3240, 784, 832, 4032, 1408, 1280, 0, 0, 0, 0],
    ![2734, 1312, 392, 1328, 1792, 1536, 3712, 2560, 0, 0, 0, 0],
    ![1324, 3572, 3784, 4016, 2496, 3136, 896, 1024, 3584, 3072, 0, 0],
    ![94, 884, 1848, 672, 3520, 3968, 896, 2560, 1536, 0, 0, 0]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedNinthLowerSpinCompactSecondPhaseRows : Fin 11 → Fin 12 → ℕ :=
  ![
    ![1282, 2116, 2088, 2352, 1056, 3392, 3328, 0, 2048, 0, 2048, 0],
    ![542, 1084, 680, 96, 2624, 704, 1664, 0, 0, 1024, 2048, 0],
    ![3626, 0, 3192, 3120, 608, 3072, 3712, 0, 0, 3072, 0, 0],
    ![2210, 40, 1232, 3616, 2624, 1152, 3712, 1024, 0, 0, 0, 0],
    ![454, 1412, 80, 464, 1216, 1216, 1536, 0, 1536, 1024, 0, 0],
    ![2464, 2920, 3048, 2784, 0, 0, 512, 0, 512, 2048, 0, 0],
    ![2002, 3308, 2904, 464, 1184, 2880, 2432, 1024, 0, 0, 0, 0],
    ![2416, 2524, 2136, 544, 2496, 1792, 2432, 1280, 0, 0, 0, 0],
    ![1422, 1256, 256, 1152, 2976, 3904, 1664, 512, 0, 0, 0, 0],
    ![3830, 2024, 248, 320, 1280, 64, 1152, 1280, 3072, 2048, 2048, 0],
    ![3998, 1032, 1224, 3088, 800, 2624, 1920, 1280, 1024, 3072, 2048, 0]]

/-- Number of individual normalized Fourier factors in each compact source model. -/
def generatedNinthLowerSpinCompactHadamardRank : Fin 11 → Fin 13 :=
  ![2, 2, 2, 2, 6, 4, 8, 8, 8, 10, 10]

/-- Full Pauli coordinates of the compact model, including its exact scalar sign. -/
def generatedNinthLowerSpinCompactPauliLabels : Fin 11 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(2048, 311, 0), (0, 934, 0), (1899, 1427, 0), (3947, 132, 0), (510, 1450, 0), (655, 1920, 1),
    (1511, 2729, 0), (3962, 3719, 1), (1452, 3448, 1), (2874, 3616, 0), (65, 2850, 1)]

/-- Decode an exact compact coefficient column in the original binary spin basis. -/
def generatedNinthLowerSpinCompactMatrix (a : Fin 12 → ℕ) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayBooleanCast ((a j).testBit i.val)

/-- Decode an exact upper-triangular quadratic coefficient matrix. -/
def generatedNinthLowerSpinCompactPhase (a : Fin 12 → ℕ) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => golayBooleanCast ((a i).testBit j.val)

set_option maxHeartbeats 8000000 in
-- Both two-sided products of each proposed monomial inverse use the literal binary columns.
/-- All compact monomial matrices retain their actual two-sided binary inverses. -/
theorem generatedNinth_lower_spin_compact_matrix_inverse : ∀ i : Fin 11,
    (generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactLeftInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactLeftColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactLeftColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactLeftInverseColumns i) =
          1) ∧
    (generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactRightInverseColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactRightColumns i) = 1 ∧
      generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactRightColumns i) *
        generatedNinthLowerSpinCompactMatrix (generatedNinthLowerSpinCompactRightInverseColumns i) =
          1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
