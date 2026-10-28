/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedHighPairGeneric

/-! Complete original corrected mover high-pair word checks, retaining every signed coordinate. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- All original source words, unused bits and target coefficients of the actual high pair. -/
def generatedRootEightMoverTensorHighPairCondition (j : Fin 24) (a : Fin 256) : Prop :=
  let w := generatedRootEightMoverPackedHighSources
    (fun b => generatedRootEightMoverTensorStageWords 0 j
      ⟨b.val / 16, by omega⟩ ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩) 0 1 a
  let t := generatedRootEightMoverTensorStageWords 1 j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  (∀ z : Fin 4, w z < 65536 ^ 16 ∧ w z &&& generatedRootEightPackedWideUpperMask = 0) ∧
    t < 65536 ^ 16 ∧ t &&& generatedRootEightPackedWideUpperMask = 0 ∧
      (∑ z : Fin 4, generatedRootEightMoverPackedHighCoefficients 0 1 a z *
        generatedRootEightPackedWideBiasedWord (w z)) =
          2 * generatedRootEightPackedWideBiasedWord t

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_00 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 0 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_01 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 1 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_02 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 2 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_03 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 3 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_04 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 4 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_05 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 5 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_06 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 6 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_07 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 7 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_08 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 8 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_09 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 9 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_10 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 10 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_11 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 11 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_12 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 12 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_13 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 13 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_14 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 14 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_15 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 15 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_16 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 16 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_17 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 17 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_18 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 18 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_19 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 19 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_20 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 20 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_21 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 21 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_22 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 22 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this full physical row.
private theorem row_23 : ∀ a : Fin 256, generatedRootEightMoverTensorHighPairCondition 23 a := by
  unfold generatedRootEightMoverTensorHighPairCondition
  decide +kernel

/-- Every original word and coordinate guard of the entire corrected mover high pair is checked. -/
theorem generatedRootEight_mover_tensor_high_pair_certificate (j : Fin 24) (a : Fin 256) :
    generatedRootEightMoverTensorHighPairCondition j a := by
  fin_cases j
  · exact row_00 a
  · exact row_01 a
  · exact row_02 a
  · exact row_03 a
  · exact row_04 a
  · exact row_05 a
  · exact row_06 a
  · exact row_07 a
  · exact row_08 a
  · exact row_09 a
  · exact row_10 a
  · exact row_11 a
  · exact row_12 a
  · exact row_13 a
  · exact row_14 a
  · exact row_15 a
  · exact row_16 a
  · exact row_17 a
  · exact row_18 a
  · exact row_19 a
  · exact row_20 a
  · exact row_21 a
  · exact row_22 a
  · exact row_23 a

/-- The complete word checks imply every original signed slot of the actual high Fourier pair. -/
theorem generatedRootEight_mover_tensor_high_pair_coordinates (j : Fin 24)
    (a : Fin 256) (i : Fin 16) :
    (∑ z : Fin 4, generatedRootEightMoverPackedHighCoefficients 0 1 a z *
      generatedRootEightPackedWideBiasedDigit
        (generatedRootEightMoverPackedHighSources
          (fun b => generatedRootEightMoverTensorStageWords 0 j
            ⟨b.val / 16, by omega⟩ ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩) 0 1 a z) i) =
      2 * generatedRootEightPackedWideBiasedDigit
        (generatedRootEightMoverTensorStageWords 1 j
          ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) i := by
  have h := generatedRootEight_mover_tensor_high_pair_certificate j a
  unfold generatedRootEightMoverTensorHighPairCondition at h
  have hc : (∑ z : Fin 4, |generatedRootEightMoverPackedHighCoefficients 0 1 a z|) + |(2 : ℤ)| < 256 := by
    cases h0 : a.val.testBit 0 <;> cases h1 : a.val.testBit 1 <;>
      norm_num [generatedRootEightMoverPackedHighCoefficients, h0, h1, Fin.sum_univ_succ]
  exact generatedRootEight_packed_wide_biased_bounded _ _ _ 2 hc
    (fun z => (h.1 z).1) h.2.1 (fun z => (h.1 z).2) h.2.2.1 h.2.2.2 i

/-- The first actual mover Fourier pair is proved on all4096 original labels and all physical columns. -/
theorem generatedRootEight_mover_tensor_pair_00 (j : Fin 24) : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 4
      (generatedNinthLowerSpinTensorFourierInteger 5
        (generatedRootEightMoverTensorSpinInteger 0 j)) n =
      2 * generatedRootEightMoverTensorSpinInteger 1 j n := by
  exact generatedRootEight_mover_packed_high_pair_of_coordinates
    (generatedRootEightMoverTensorStageWords 0 j) (generatedRootEightMoverTensorStageWords 1 j)
      0 1 (by decide) (generatedRootEight_mover_tensor_high_pair_coordinates j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
