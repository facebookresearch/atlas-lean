/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFifthMiddleFiniteRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthComparisonWords

/-! A complete actual middle pairing proves the two genuine Fifth destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

private theorem fifth_pairing_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete inverse-triality framed vector, without any recognition hypothesis. -/
def generatedAxisGlobalOddFifthMiddleComparison (k : Fin 2) : GriessSpace :=
  sExtra.symm (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)
    ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis))

/-- Its actual squared norm is preserved by all original genuine source operations. -/
theorem generatedAxisGlobalOddFifthMiddleComparison_norm (k : Fin 2) :
    griessForm (generatedAxisGlobalOddFifthMiddleComparison k)
      (generatedAxisGlobalOddFifthMiddleComparison k) = 128 := by
  have h := sExtra_preserves_griessForm
    (generatedAxisGlobalOddFifthMiddleComparison k) (generatedAxisGlobalOddFifthMiddleComparison k)
  rw [generatedAxisGlobalOddFifthMiddleComparison, sExtra.apply_symm_apply,
    rhoLocal_form, generated_group_preserves_griessForm, generatedAxisGlobalOdd_norm] at h
  exact h.symm

/-- Equal actual norms and an exact complete pairing prove equality of the whole middle vectors. -/
theorem generatedAxisGlobalOddFifthMiddleComparison_eq_of_pairing (k : Fin 2)
    (hp : griessForm (generatedAxisGlobalOddFifthMiddleComparison k)
      generatedAxisGlobalCanonicalFifthMiddleAxis = 128) :
    generatedAxisGlobalOddFifthMiddleComparison k =
      generatedAxisGlobalCanonicalFifthMiddleAxis := by
  apply sub_eq_zero.mp
  apply (griessForm_self_eq_zero_iff _).mp
  simp only [map_sub, LinearMap.sub_apply]
  rw [generatedAxisGlobalOddFifthMiddleComparison_norm,
    generatedAxisGlobalCanonicalFifthMiddle_norm, hp,
    fifth_pairing_symm generatedAxisGlobalCanonicalFifthMiddleAxis _, hp]
  ring

/-- The complete middle equality identifies the whole actual outgoing axis with canonical Fifth. -/
theorem generatedAxisGlobalOddFifthDestination_of_pairing (k : Fin 2)
    (hp : griessForm (generatedAxisGlobalOddFifthMiddleComparison k)
      generatedAxisGlobalCanonicalFifthMiddleAxis = 128) :
    rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis) =
        generatedFifthAxis := by
  have h := congrArg sExtra (generatedAxisGlobalOddFifthMiddleComparison_eq_of_pairing k hp)
  rw [generatedAxisGlobalOddFifthMiddleComparison, sExtra.apply_symm_apply,
    generatedAxisGlobalCanonicalFifthMiddle_triality] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
