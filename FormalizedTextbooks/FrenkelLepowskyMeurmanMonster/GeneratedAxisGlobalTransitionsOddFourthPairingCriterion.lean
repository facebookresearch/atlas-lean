/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthMiddleFiniteRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthComparisonWords

/-! A complete actual middle pairing proves the four genuine Fourth destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

private theorem fourth_pairing_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete inverse-triality framed vector, without any recognition hypothesis. -/
def generatedAxisGlobalOddFourthMiddleComparison (k : Fin 4) : GriessSpace :=
  sExtra.symm (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k)
    ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis))

/-- Its actual squared norm is preserved by all original genuine source operations. -/
theorem generatedAxisGlobalOddFourthMiddleComparison_norm (k : Fin 4) :
    griessForm (generatedAxisGlobalOddFourthMiddleComparison k)
      (generatedAxisGlobalOddFourthMiddleComparison k) = 128 := by
  have h := sExtra_preserves_griessForm
    (generatedAxisGlobalOddFourthMiddleComparison k) (generatedAxisGlobalOddFourthMiddleComparison k)
  rw [generatedAxisGlobalOddFourthMiddleComparison, sExtra.apply_symm_apply,
    rhoLocal_form, generated_group_preserves_griessForm, generatedAxisGlobalOdd_norm] at h
  exact h.symm

/-- Equal actual norms and an exact complete pairing prove equality of the whole middle vectors. -/
theorem generatedAxisGlobalOddFourthMiddleComparison_eq_of_pairing (k : Fin 4)
    (hp : griessForm (generatedAxisGlobalOddFourthMiddleComparison k)
      generatedAxisGlobalCanonicalFourthMiddleAxis = 128) :
    generatedAxisGlobalOddFourthMiddleComparison k = generatedAxisGlobalCanonicalFourthMiddleAxis := by
  apply sub_eq_zero.mp
  apply (griessForm_self_eq_zero_iff _).mp
  simp only [map_sub, LinearMap.sub_apply]
  rw [generatedAxisGlobalOddFourthMiddleComparison_norm,
    generatedAxisGlobalCanonicalFourthMiddle_norm, hp,
    fourth_pairing_symm generatedAxisGlobalCanonicalFourthMiddleAxis _, hp]
  ring

/-- The complete middle equality identifies the whole actual outgoing axis with canonical Fourth. -/
theorem generatedAxisGlobalOddFourthDestination_of_pairing (k : Fin 4)
    (hp : griessForm (generatedAxisGlobalOddFourthMiddleComparison k)
      generatedAxisGlobalCanonicalFourthMiddleAxis = 128) :
    rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k)
      ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis) = generatedFourthAxis := by
  have h := congrArg sExtra (generatedAxisGlobalOddFourthMiddleComparison_eq_of_pairing k hp)
  rw [generatedAxisGlobalOddFourthMiddleComparison, sExtra.apply_symm_apply,
    generatedAxisGlobalCanonicalFourthMiddle_triality] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
