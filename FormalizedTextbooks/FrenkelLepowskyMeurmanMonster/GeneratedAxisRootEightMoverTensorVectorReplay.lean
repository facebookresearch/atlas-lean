/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorSpinAction

/-! Whole genuine mover action from original complete integer coordinate certificates. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The original corrected mover post action on every output column. -/
def generatedRootEightMoverTensorSpinOutput (r : Fin 24) : NortonUIntegerVector :=
  generatedRootEightMoverTensorPostInteger (generatedRootEightMoverTensorSpinInteger 3 r)

/-- Every actual canonical tensor coordinate has its proved original raw cache scale. -/
theorem generatedRootEight_canonical_tensor_raw_actual (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
      (generatedRootEightCanonicalTensorRawCache (nortonUIntegerLabel t) i : ℝ) /
        (16 * Real.sqrt 2) := by
  rw [generatedRootEight_canonical_tensor_cache_of_integer_binding
    generatedRootEight_canonical_positive_tensor_integer,
    generatedRootEight_canonical_tensor_raw_cache_scale]
  push_cast
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]
  ring

/-- Three full original pair certificates replay the entire genuine corrected mover spin. -/
theorem generatedRootEight_mover_tensor_vector_replay (r : Fin 24) (v : NortonUIntegerVector)
    (ha : ∀ n, generatedRootEightMoverTensorAddressCondition n)
    (hf : ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (hs : ∀ n, generatedRootEightMoverTensorSpinInteger 0 r n =
      8 * generatedRootEightMoverTensorPreInteger v n)
    (h0 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 4
      (generatedNinthLowerSpinTensorFourierInteger 5
        (generatedRootEightMoverTensorSpinInteger 0 r)) n =
          2 * generatedRootEightMoverTensorSpinInteger 1 r n)
    (h1 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightMoverTensorSpinInteger 1 r)) n =
          2 * generatedRootEightMoverTensorSpinInteger 2 r n)
    (h2 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 0
      (generatedNinthLowerSpinTensorFourierInteger 1
        (generatedRootEightMoverTensorSpinInteger 2 r)) n =
          2 * generatedRootEightMoverTensorSpinInteger 3 r n) :
    generatedRootEightMoverCorrectedFiber.val.1.val ((8 : ℝ) • nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMoverTensorSpinOutput r) := by
  have hp : generatedRootEightMoverTensorPre.val ((8 : ℝ) • nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMoverTensorSpinInteger 0 r) := by
    rw [map_smul, generatedRootEight_mover_tensor_pre_embed ha]
    ext t
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, hs,
      Int.cast_mul, Int.cast_ofNat]
  have p0 := generatedNinth_lower_spin_tensor_pair_embed (4, 5) hf _ _ h0
  have p1 := generatedNinth_lower_spin_tensor_pair_embed (2, 3) hf _ _ h1
  have p2 := generatedNinth_lower_spin_tensor_pair_embed (0, 1) hf _ _ h2
  rw [generatedRootEight_mover_tensor_compact_factorization]
  change generatedRootEightMoverTensorPost.val
    ((generatedNinthLowerSpinTensorPair (0, 1)).val
      ((generatedNinthLowerSpinTensorPair (2, 3)).val
        ((generatedNinthLowerSpinTensorPair (4, 5)).val
          (generatedRootEightMoverTensorPre.val ((8 : ℝ) • nortonUIntegerEmbed v))))) = _
  rw [hp, p0, p1, p2, generatedRootEight_mover_tensor_post_embed ha]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
