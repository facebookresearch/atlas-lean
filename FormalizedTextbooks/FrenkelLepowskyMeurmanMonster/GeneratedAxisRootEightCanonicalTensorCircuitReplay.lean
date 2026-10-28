/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCircuitActions

/-! Whole-vector replay of the genuine canonical compact spin circuit from finite certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All original canonical output spin coefficients, retaining the complete actual Pauli post action. -/
def generatedRootEightCanonicalTensorSpinInteger (r : Fin 24) : NortonUIntegerVector :=
  generatedRootEightCanonicalTensorPostInteger (generatedRootEightCanonicalTensorStageInteger 4 r)

/-- Four exact pair certificates act on the entire original source vector. -/
theorem generatedRootEight_canonical_tensor_circuit_replay (r : Fin 24)
    (ha : ∀ n, generatedRootEightCanonicalTensorAddressCondition n)
    (hf : ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (hs : ∀ n, generatedRootEightCanonicalTensorStageInteger 0 r n =
      16 * generatedRootEightCanonicalTensorPreInteger
        (generatedRootEightCanonicalTensorSourceCache r) n)
    (h0 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 6
      (generatedNinthLowerSpinTensorFourierInteger 7
        (generatedRootEightCanonicalTensorStageInteger 0 r)) n =
          2 * generatedRootEightCanonicalTensorStageInteger 1 r n)
    (h1 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 4
      (generatedNinthLowerSpinTensorFourierInteger 5
        (generatedRootEightCanonicalTensorStageInteger 1 r)) n =
          2 * generatedRootEightCanonicalTensorStageInteger 2 r n)
    (h2 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (generatedRootEightCanonicalTensorStageInteger 2 r)) n =
          2 * generatedRootEightCanonicalTensorStageInteger 3 r n)
    (h3 : ∀ n, generatedNinthLowerSpinTensorFourierInteger 0
      (generatedNinthLowerSpinTensorFourierInteger 1
        (generatedRootEightCanonicalTensorStageInteger 3 r)) n =
          2 * generatedRootEightCanonicalTensorStageInteger 4 r n) :
    (generatedRootEightCompactSpin 12).val
      ((16 : ℝ) • nortonUIntegerEmbed (generatedRootEightCanonicalTensorSourceCache r)) =
        nortonUIntegerEmbed (generatedRootEightCanonicalTensorSpinInteger r) := by
  have hp : generatedRootEightCanonicalTensorPre.val
      ((16 : ℝ) • nortonUIntegerEmbed (generatedRootEightCanonicalTensorSourceCache r)) =
        nortonUIntegerEmbed (generatedRootEightCanonicalTensorStageInteger 0 r) := by
    rw [map_smul, generatedRootEight_canonical_tensor_pre_embed ha]
    ext t
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, hs,
      Int.cast_mul, Int.cast_ofNat]
  have p0 := generatedNinth_lower_spin_tensor_pair_embed (6, 7) hf _ _ h0
  have p1 := generatedNinth_lower_spin_tensor_pair_embed (4, 5) hf _ _ h1
  have p2 := generatedNinth_lower_spin_tensor_pair_embed (2, 3) hf _ _ h2
  have p3 := generatedNinth_lower_spin_tensor_pair_embed (0, 1) hf _ _ h3
  rw [generatedRootEight_canonical_tensor_compact_factorization]
  change generatedRootEightCanonicalTensorPost.val
    ((generatedNinthLowerSpinTensorPair (0, 1)).val
      ((generatedNinthLowerSpinTensorPair (2, 3)).val
        ((generatedNinthLowerSpinTensorPair (4, 5)).val
          ((generatedNinthLowerSpinTensorPair (6, 7)).val
            (generatedRootEightCanonicalTensorPre.val
              ((16 : ℝ) • nortonUIntegerEmbed
                (generatedRootEightCanonicalTensorSourceCache r))))))) = _
  rw [hp, p0, p1, p2, p3, generatedRootEight_canonical_tensor_post_embed ha]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
