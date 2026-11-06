/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinHadamard
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedData

/-! Exact compact integer data and two-sided binary matrix inverse certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactLeftColumns : Fin 12 → Fin 12 → ℕ :=
  ![    ![2048, 1198, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512],
    ![2144, 324, 2151, 99, 2048, 270, 1, 8, 16, 128, 512, 1024],
    ![208, 7, 960, 211, 2048, 3197, 1, 8, 16, 32, 64, 256],
    ![2048, 3, 1, 4, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![2048, 4, 1, 2, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![2048, 9, 1, 2, 4, 16, 32, 64, 128, 256, 512, 1024],
    ![2048, 96, 1, 2, 4, 8, 16, 32, 128, 256, 512, 1024],
    ![2048, 176, 1, 2, 4, 8, 16, 32, 64, 256, 512, 1024],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactLeftInverseColumns : Fin 12 → Fin 12 → ℕ :=
  ![    ![4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 698, 1],
    ![64, 89, 28, 128, 256, 234, 251, 512, 229, 1024, 2048, 16],
    ![64, 73, 11, 128, 256, 512, 1024, 1281, 2048, 2309, 2043, 16],
    ![4, 6, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 1],
    ![4, 8, 2, 16, 32, 64, 128, 256, 512, 1024, 2048, 1],
    ![4, 8, 16, 6, 32, 64, 128, 256, 512, 1024, 2048, 1],
    ![4, 8, 16, 32, 64, 128, 130, 256, 512, 1024, 2048, 1],
    ![4, 8, 16, 32, 64, 128, 256, 194, 512, 1024, 2048, 1],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactRightColumns : Fin 12 → Fin 12 → ℕ :=
  ![    ![2328, 2196, 16, 2224, 2197, 2500, 2520, 924, 3268, 3300, 2240, 2],
    ![3520, 3521, 2, 3584, 3136, 64, 76, 3264, 68, 2112, 1236, 32],
    ![2560, 3072, 4, 2569, 2688, 2816, 3331, 320, 208, 257, 4032, 32],
    ![4, 5, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 2],
    ![4, 8, 1, 16, 32, 64, 128, 256, 512, 1024, 2048, 2],
    ![4, 8, 16, 5, 32, 64, 128, 256, 512, 1024, 2048, 2],
    ![4, 8, 16, 32, 64, 128, 129, 256, 512, 1024, 2048, 2],
    ![4, 8, 16, 32, 64, 128, 256, 193, 512, 1024, 2048, 2],
    ![1, 2, 4, 8, 19, 42, 74, 141, 266, 522, 1124, 2048],
    ![1, 2, 4, 8, 25, 35, 71, 138, 256, 522, 1204, 2048],
    ![15, 8, 4, 2, 192, 64, 32, 48, 256, 512, 1024, 2048],
    ![8, 15, 4, 1, 160, 240, 144, 224, 432, 720, 1024, 2048]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactRightInverseColumns : Fin 12 → Fin 12 → ℕ :=
  ![    ![18, 2048, 778, 878, 4, 768, 1804, 1869, 1834, 135, 1546, 1089],
    ![3, 4, 288, 320, 1920, 2048, 32, 144, 129, 56, 528, 544],
    ![545, 578, 4, 552, 432, 2048, 161, 17, 33, 1171, 1168, 1170],
    ![3, 2048, 1, 4, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![4, 2048, 1, 2, 8, 16, 32, 64, 128, 256, 512, 1024],
    ![9, 2048, 1, 2, 4, 16, 32, 64, 128, 256, 512, 1024],
    ![96, 2048, 1, 2, 4, 8, 16, 32, 128, 256, 512, 1024],
    ![176, 2048, 1, 2, 4, 8, 16, 32, 64, 256, 512, 1024],
    ![1, 2, 4, 8, 19, 42, 74, 141, 266, 522, 1124, 2048],
    ![1, 2, 4, 8, 25, 35, 71, 138, 256, 522, 1204, 2048],
    ![15, 8, 4, 2, 192, 64, 32, 48, 256, 512, 1024, 2048],
    ![8, 15, 4, 1, 160, 240, 144, 224, 432, 720, 1024, 2048]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactFirstPhaseRows : Fin 12 → Fin 12 → ℕ :=
  ![    ![514, 1368, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1708, 3716, 1024, 1824, 1984, 1856, 0, 0, 0, 0, 0, 0],
    ![1252, 4000, 2760, 2912, 3808, 1344, 0, 0, 0, 0, 0, 0],
    ![2, 2052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 1580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 1068, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Exact compact binary coefficients in the original twelve spin coordinates. -/
def generatedTwelfthSpinCompactSecondPhaseRows : Fin 12 → Fin 12 → ℕ :=
  ![    ![966, 512, 2048, 3648, 3520, 384, 2432, 256, 3584, 3072, 2048, 0],
    ![2112, 1488, 2520, 384, 1312, 448, 1408, 256, 1024, 3072, 2048, 0],
    ![2880, 2384, 2320, 1792, 384, 3840, 1408, 1280, 512, 2048, 2048, 0],
    ![2054, 0, 2048, 0, 0, 1280, 640, 1280, 512, 1024, 0, 0],
    ![30, 0, 2048, 2048, 2048, 960, 1792, 1792, 1024, 0, 0, 0],
    ![2054, 0, 2048, 0, 0, 1664, 1408, 768, 1536, 1024, 0, 0],
    ![1582, 0, 64, 1984, 0, 1664, 1024, 1536, 512, 0, 0, 0],
    ![1070, 0, 192, 1152, 0, 1344, 1536, 512, 512, 0, 0, 0],
    ![1040, 2032, 0, 1888, 480, 896, 896, 512, 1024, 1024, 0, 0],
    ![1072, 1696, 0, 1744, 480, 896, 896, 512, 0, 1024, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 256, 768, 768, 512, 512, 0, 0, 0]]

/-- Number of individual normalized Fourier factors in each compact source model. -/
def generatedTwelfthSpinCompactHadamardRank : Fin 12 → Fin 13 :=
  ![2, 6, 6, 2, 2, 2, 2, 2, 0, 0, 0, 0]

/-- Full Pauli coordinates of the compact model, including its exact scalar sign. -/
def generatedTwelfthSpinCompactPauliLabels : Fin 12 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(2366, 1425, 0), (139, 3420, 1), (760, 2699, 1), (3, 1208, 1), (2052, 395, 1), (13, 226, 0),
    (96, 1027, 1), (2228, 1176, 0), (7, 1539, 1), (7, 808, 0), (212, 10, 1), (212, 1506, 0)]

/-- Decode an exact compact coefficient column in the original binary spin basis. -/
def generatedTwelfthSpinCompactMatrix (a : Fin 12 → ℕ) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayBooleanCast ((a j).testBit i.val)

/-- Decode an exact upper-triangular quadratic coefficient matrix. -/
def generatedTwelfthSpinCompactPhase (a : Fin 12 → ℕ) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => golayBooleanCast ((a i).testBit j.val)

set_option maxHeartbeats 8000000 in
-- Both two-sided products of each proposed monomial inverse use the literal binary columns.
/-- All compact monomial matrices retain their actual two-sided binary inverses. -/
theorem generatedTwelfth_spin_compact_matrix_inverse : ∀ i : Fin 12,
    (generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactLeftInverseColumns i) *
        generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactLeftColumns i) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactLeftColumns i) *
        generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactLeftInverseColumns i) =
          1) ∧
    (generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactRightInverseColumns i) *
        generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactRightColumns i) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactRightColumns i) *
        generatedTwelfthSpinCompactMatrix (generatedTwelfthSpinCompactRightInverseColumns i) =
          1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
