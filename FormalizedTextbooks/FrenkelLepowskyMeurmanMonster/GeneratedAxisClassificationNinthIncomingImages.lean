/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhysicalCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! The complete original incoming odd-column inverse identifies actual short permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual preferred odd-short target in physical column one. -/
def generatedNinthIncomingTargetIndex (d : Fin 2048) : GriessShortIndex :=
  Sum.inr (Sum.inr (d, 1))

/-- The original inverse matrix sends every incoming odd target to its preferred source. -/
theorem generatedNinth_incoming_inverse_numerator (d : Fin 2048) (i : Fin 24) :
    (generatedNinthInverseNumerator *ᵥ griessShortIntegral
      (generatedNinthIncomingTargetIndex d)) i =
        8 * generatedNinthIncomingPhysicalSign d *
          generatedNinthIncomingShortIntegral (generatedNinthIncomingSource d) i := by
  exact generatedNinth_incoming_physical_certificate d i

/-- The actual inverse local isometry retains the source's physical sign. -/
theorem generatedNinth_incoming_inverse_vector (d : Fin 2048) :
    generatedNinthLocalFiber.val.2.val.symm
        (griessShortVector (generatedNinthIncomingTargetIndex d)) =
      (generatedNinthIncomingPhysicalSign d : ℝ) •
        griessShortVector (generatedNinthIncomingShortIndex (generatedNinthIncomingSource d)) := by
  funext i
  rw [generatedNinth_inverse_short_coordinate, generatedNinth_incoming_inverse_numerator]
  simp only [Int.cast_mul, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul, griessShortVector,
    ← generatedNinthIncomingShortIntegral_actual]
  ring

/-- Original line uniqueness identifies the genuine inverse preferred-short permutation. -/
theorem generatedNinth_incoming_inverse_permutation (d : Fin 2048) :
    griessShortPermutation (generatedNinthLocalFiber.val.2⁻¹)
        (generatedNinthIncomingTargetIndex d) =
      generatedNinthIncomingShortIndex (generatedNinthIncomingSource d) := by
  have h := generatedNinth_incoming_inverse_vector d
  rcases griessShortPermutation_vector (generatedNinthLocalFiber.val.2⁻¹)
    (generatedNinthIncomingTargetIndex d) with hv | hv
  · exact centralizer_shortVector_line_unique _ _ _ (hv.symm.trans h)
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedNinthIncomingPhysicalSign d : ℝ))
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg (hv.symm.trans h)

/-- The actual forward short permutation sends every preferred source
to its original odd target. -/
theorem generatedNinth_incoming_forward_permutation (d : Fin 2048) :
    griessShortPermutation generatedNinthLocalFiber.val.2
        (generatedNinthIncomingShortIndex (generatedNinthIncomingSource d)) =
      generatedNinthIncomingTargetIndex d := by
  have h := congrArg (griessShortPermutation generatedNinthLocalFiber.val.2)
    (generatedNinth_incoming_inverse_permutation d)
  simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h.symm

/-- The full original local short operator retains the genuine preferred-Q phase. -/
theorem generatedNinth_incoming_operator (d : Fin 2048) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedNinthLocalFiber X (generatedNinthIncomingTargetIndex d) =
      qSign (localShortPhase generatedNinthLocalFiber
        (generatedNinthIncomingShortIndex (generatedNinthIncomingSource d))) *
          X (generatedNinthIncomingShortIndex (generatedNinthIncomingSource d)) := by
  rw [← generatedNinth_incoming_forward_permutation d]
  exact localShortOperator_image _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
