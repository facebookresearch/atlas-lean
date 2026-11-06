/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Form preservation for every element of the actual generated group.
This uses the proved form laws of both generating pieces.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The stabilizer of the actual weighted Griess form. -/
noncomputable def griessFormSubgroup : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) where
  carrier := {e | ∀ x y, griessForm (e x) (e y) = griessForm x y}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro a b ha hb x y
    change griessForm (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have h := ha (a.symm x) (a.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- Form preservation is already established for the entire generated group,
independently of the remaining product preservation obligations. -/
theorem G_le_griessFormSubgroup : G ≤ griessFormSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨h, rfl⟩ | he)
  · exact rhoLocal_form h
  · have heq : e = sExtra := Set.mem_singleton_iff.mp he
    subst e
    exact sExtra_preserves_griessForm

theorem generated_group_preserves_griessForm (g : ↥G) (x y : GriessSpace) :
    griessForm (g.val x) (g.val y) = griessForm x y :=
  G_le_griessFormSubgroup g.property x y

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
