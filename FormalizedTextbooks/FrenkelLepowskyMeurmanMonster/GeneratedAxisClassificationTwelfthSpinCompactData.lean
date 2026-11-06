/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactMatrixCertificates

/-! Genuine compact spin factors from previously certified whole binary inverse matrices. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- An exact invertible binary matrix gives an actual spin-coordinate linear equivalence. -/
def generatedTwelfthSpinCompactEquiv (a b : Fin 12 → ℕ)
    (hleft : generatedTwelfthSpinCompactMatrix b *
      generatedTwelfthSpinCompactMatrix a = 1)
    (hright : generatedTwelfthSpinCompactMatrix a *
      generatedTwelfthSpinCompactMatrix b = 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := generatedTwelfthSpinCompactMatrix a *ᵥ t
  invFun t := generatedTwelfthSpinCompactMatrix b *ᵥ t
  left_inv t := by
    change generatedTwelfthSpinCompactMatrix b *ᵥ
      (generatedTwelfthSpinCompactMatrix a *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  right_inv t := by
    change generatedTwelfthSpinCompactMatrix a *ᵥ
      (generatedTwelfthSpinCompactMatrix b *ᵥ t) = t
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- The exact compact left binary monomial is an actual spin-coordinate equivalence. -/
def generatedTwelfthSpinCompactLeft (i : Fin 12) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTwelfthSpinCompactLeftColumns i)
    (generatedTwelfthSpinCompactLeftInverseColumns i)
    (generatedTwelfth_spin_compact_matrix_inverse i).1.1
    (generatedTwelfth_spin_compact_matrix_inverse i).1.2

/-- The exact compact right binary monomial is an actual spin-coordinate equivalence. -/
def generatedTwelfthSpinCompactRight (i : Fin 12) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTwelfthSpinCompactRightColumns i)
    (generatedTwelfthSpinCompactRightInverseColumns i)
    (generatedTwelfth_spin_compact_matrix_inverse i).2.1
    (generatedTwelfth_spin_compact_matrix_inverse i).2.2

/-- The exact compact source Pauli is an element of the original extraspecial group. -/
def generatedTwelfthSpinCompactPauli (i : Fin 12) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedTwelfthSpinCompactPauliLabels i).1)
    (golayLabelCoefficients (generatedTwelfthSpinCompactPauliLabels i).2.1)),
    ofAdd (generatedTwelfthSpinCompactPauliLabels i).2.2⟩

/-- Individual Fourier factors use precisely the first prescribed original coordinates. -/
def generatedTwelfthSpinCompactHadamardWord (i : Fin 12) : List (Fin 12) :=
  (List.finRange 12).filter (fun k => k.val < (generatedTwelfthSpinCompactHadamardRank i).val)

/-- Every compact model is a product of genuine orthogonal spin normalizer elements. -/
def generatedTwelfthSpinCompact (i : Fin 12) : SpinHolomorph :=
  spinHolomorphIncl (generatedTwelfthSpinCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedTwelfthSpinCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactFirstPhaseRows i)) *
    ((generatedTwelfthSpinCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedTwelfthSpinCompactRight i)

/-- Complete original spatial source words of the twelve proposed whole-axis lifts. -/
def generatedTwelfthSpinCompactSpatialWord : Fin 12 → List (Fin 18 × Bool) :=
  ![    [(16, true), (15, true), (16, true), (16, true), (4, true), (15, true), (16, false), (4,
    false), (16, false), (16, false), (12, false), (13, false), (7, false)],
    [(15, true), (17, true), (16, true), (0, true), (16, true), (17, false), (4, false), (16,
    false), (16, false), (12, false), (13, false), (7, false)],
    [(5, true), (8, true), (12, true), (14, true), (13, true), (16, true), (17, false), (14,
    false), (13, false), (16, false), (8, false), (14, false), (10, false)],
    [(0, false), (1, false)],
    [(2, false)],
    [(0, false), (3, false)],
    [(5, false), (6, false)],
    [(4, false), (5, false), (7, false)],
    [(13, false), (12, false), (14, false), (12, false), (13, false), (15, false), (13, false),
    (12, false), (14, false), (12, false), (13, false), (15, false), (13, false), (15, false),
    (13, false), (15, false), (13, false), (15, false), (13, false), (13, false), (12, false),
    (13, false), (12, false), (13, false), (15, false), (13, false), (15, false), (13, false)],
    [(15, false), (13, false), (15, false), (13, false), (13, false), (12, false), (14, false),
    (12, false), (13, false), (12, false), (14, false), (12, false), (13, false), (12, false),
    (14, false), (12, false), (15, false), (13, false), (15, false), (13, false), (13, false),
    (12, false), (14, false), (12, false), (13, false), (12, false), (14, false), (12, false),
    (13, false), (12, false), (14, false), (12, false)],
    [(13, false), (12, false), (14, false), (12, false), (13, false), (12, false), (14, false),
    (12, false), (13, false), (12, false), (14, false), (12, false), (15, false), (13, false),
    (15, false), (13, false), (13, false), (12, false), (13, false), (12, false), (13, false),
    (15, false), (13, false), (15, false), (13, false), (15, false), (13, false), (15, false),
    (13, false), (15, false), (13, false), (15, false), (13, false), (13, false), (12, false),
    (13, false), (12, false), (13, false), (15, false), (13, false), (15, false), (13, false),
    (13, false), (12, false), (14, false), (12, false), (13, false), (12, false), (14, false),
    (12, false), (13, false), (12, false), (14, false), (12, false)],
    [(13, false), (12, false), (14, false), (12, false), (13, false), (15, false), (13, false),
    (12, false), (14, false), (12, false), (13, false), (13, false), (12, false), (14, false),
    (12, false), (13, false), (12, false), (14, false), (12, false), (13, false), (12, false),
    (14, false), (12, false), (13, false), (12, false), (13, false), (12, false), (13, false),
    (13, false), (12, false), (14, false), (12, false), (13, false), (13, false), (12, false),
    (15, false), (16, false), (12, false), (15, false), (15, false), (13, false), (15, false),
    (13, false), (13, false), (12, false), (13, false), (12, false), (13, false), (15, false),
    (13, false), (15, false), (13, false), (15, false), (13, false), (15, false), (13, false),
    (13, false), (12, false), (14, false), (12, false), (13, false), (15, false), (13, false),
    (12, false), (14, false), (12, false), (13, false), (13, false), (12, false), (14, false),
    (12, false), (13, false), (12, false), (14, false), (12, false), (13, false), (12, false),
    (14, false), (12, false), (13, false), (12, false), (13, false), (12, false), (13, false),
    (13, false), (12, false), (14, false), (12, false), (13, false), (13, false), (12, false),
    (15, false), (16, false), (12, false), (15, false), (15, false), (13, false), (15, false),
    (13, false), (13, false), (12, false), (13, false), (12, false), (13, false), (15, false),
    (13, false), (15, false), (13, false)]]

/-- Every proposed source word retains all twenty-four binary coordinate columns. -/
def generatedTwelfthSpinCompactBinaryColumns : Fin 12 → Fin 24 → ℕ :=
  ![    ![2144838, 5222949, 3604484, 2210348, 5621387, 2429553, 203382, 3228745, 8043313, 3980089,
    8311344, 2048, 2752512, 1325056, 745472, 1519616, 526336, 4464640, 2236416, 4718592, 4698112,
    5746688, 7798784, 9790638],
    ![5900055, 1578775, 919552, 4886467, 4620047, 15388748, 10121288, 10336073, 12171311,
    13128779, 3711744, 4065280, 4171872, 4106336, 7258436, 524288, 4096000, 7084135, 2826339,
    4077568, 3190788, 4831232, 2734080, 2978062],
    ![6357556, 7078532, 505856, 7680564, 11708988, 13297053, 13860141, 4020095, 10595097,
    10008489, 14754221, 1507328, 458960, 2457607, 5944256, 3879123, 14336, 4196355, 5734407,
    34816, 8304640, 4194308, 4063232, 13466749],
    ![4196353, 4196354, 4, 8, 2621456, 1310752, 2752576, 1376384, 2752768, 1376768, 15360, 2048,
    6144, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    12595203],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080,
    2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8433668],
    ![4196353, 2, 4, 4196360, 3407888, 2883616, 1769536, 3539072, 2949376, 1769984, 39936, 2048,
    6144, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 12619785],
    ![67585, 4130818, 4, 3541000, 2109456, 3186720, 3186752, 1056896, 960768, 502272, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 264192, 524288, 1048576, 2097152, 4194304, 11579488],
    ![198657, 2754562, 4, 2951176, 3182608, 1060896, 1081408, 2138240, 459008, 633344, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 133120, 262144, 526336, 1048576, 2097152, 4194304, 10530992],
    ![4259841, 8323074, 4, 7733256, 2109459, 3186730, 3186762, 1056909, 5153034, 4694538, 3191908,
    2048, 593920, 3612672, 4734976, 4096000, 65536, 4325376, 4456448, 524288, 1048576, 2097152,
    4194304, 8388608],
    ![4390913, 6946818, 4, 7143432, 3182617, 1060899, 1081415, 2138250, 459008, 4825610, 2143412,
    2048, 462848, 3022848, 4472832, 2719744, 4259840, 4325376, 262144, 4718592, 1048576, 2097152,
    4194304, 8388608],
    ![15, 8, 4, 2, 192, 64, 32, 48, 256, 512, 1024, 2048, 4096, 36864, 20480, 12288, 524288,
    786432, 196608, 65536, 1048576, 2097152, 4194304, 8388608],
    ![8, 15, 4, 1, 1048736, 3145968, 3145872, 2097376, 2556336, 1966800, 1024, 2048, 40960, 8192,
    24576, 12288, 3538944, 1769472, 2752512, 4128768, 1048576, 2097152, 4194304, 8388608]]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
