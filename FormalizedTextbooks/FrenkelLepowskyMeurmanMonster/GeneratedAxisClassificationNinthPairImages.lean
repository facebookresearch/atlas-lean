/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! The original integer certificates identify the actual preferred-short permutation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original preferred target pair label in the actual short catalogue. -/
def generatedNinthPairTargetIndex (r : Fin 552) : GriessShortIndex :=
  Sum.inl ((generatedNinthPairTarget r).1,
    griessPairIndex (generatedNinthPairTarget r).2.1 (generatedNinthPairTarget r).2.2
      (ne_of_lt (generatedNinthPairTarget_lt r)))

/-- Actual preferred target vectors have their original physical pair formula. -/
theorem generatedNinth_pair_target_integral (r : Fin 552) :
    griessShortIntegral (generatedNinthPairTargetIndex r) = fun i =>
      4 * (if i = (generatedNinthPairTarget r).2.1 then 1 else 0) +
        (if (generatedNinthPairTarget r).1 = 0 then -4 else 4) *
          (if i = (generatedNinthPairTarget r).2.2 then 1 else 0) := by
  simp only [generatedNinthPairTargetIndex, griessShortIntegral, griessPairIndex_coordinates,
    generatedNinthPairTarget_lt r, ite_true]

/-- The denominator-cleared actual inverse action is exactly the recorded source vector. -/
theorem generatedNinth_pair_inverse_numerator (r : Fin 552) (i : Fin 24) :
    (generatedNinthInverseNumerator *ᵥ griessShortIntegral (generatedNinthPairTargetIndex r)) i =
      8 * generatedNinthPairPhysicalSign r *
        generatedNinthInputShortIntegral (generatedNinthPairSource r) i := by
  rw [generatedNinth_pair_target_integral]
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, mul_one]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simpa only [mul_comm, ite_mul] using generatedNinth_pair_inverse_certificate r i

/-- The genuine inverse local isometry sends each target short vector
to its preferred source line. -/
theorem generatedNinth_pair_inverse_vector (r : Fin 552) :
    generatedNinthLocalFiber.val.2.val.symm
        (griessShortVector (generatedNinthPairTargetIndex r)) =
      (generatedNinthPairPhysicalSign r : ℝ) •
        griessShortVector (generatedNinthInputShortIndex (generatedNinthPairSource r)) := by
  funext i
  rw [generatedNinth_inverse_short_coordinate, generatedNinth_pair_inverse_numerator]
  simp only [Int.cast_mul, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul, griessShortVector,
    ← generatedNinthInputShortIntegral_actual]
  ring

/-- The certified inverse short permutation uses the exact actual source catalogue label. -/
theorem generatedNinth_pair_inverse_permutation (r : Fin 552) :
    griessShortPermutation (generatedNinthLocalFiber.val.2⁻¹) (generatedNinthPairTargetIndex r) =
      generatedNinthInputShortIndex (generatedNinthPairSource r) := by
  have h := generatedNinth_pair_inverse_vector r
  rcases griessShortPermutation_vector (generatedNinthLocalFiber.val.2⁻¹)
    (generatedNinthPairTargetIndex r) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedNinthPairPhysicalSign r : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

/-- The actual forward permutation sends every preferred source to its recorded target. -/
theorem generatedNinth_pair_forward_permutation (r : Fin 552) :
    griessShortPermutation generatedNinthLocalFiber.val.2
        (generatedNinthInputShortIndex (generatedNinthPairSource r)) =
      generatedNinthPairTargetIndex r := by
  have h := congrArg (griessShortPermutation generatedNinthLocalFiber.val.2)
    (generatedNinth_pair_inverse_permutation r)
  simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h.symm

/-- Every target short coefficient is its actual forward preferred-Q phase times its source. -/
theorem generatedNinth_pair_operator (r : Fin 552) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedNinthLocalFiber X (generatedNinthPairTargetIndex r) =
      qSign (localShortPhase generatedNinthLocalFiber
        (generatedNinthInputShortIndex (generatedNinthPairSource r))) *
          X (generatedNinthInputShortIndex (generatedNinthPairSource r)) := by
  rw [← generatedNinth_pair_forward_permutation r]
  exact localShortOperator_image _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
