/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardFlagPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardSignFiber

/-! The whole actual standard flag group acts on the entire six-coordinate outside support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Membership in the entire nonzero outside support of the standard norm-twelve vector. -/
def generatedTenthE7StandardOutside (i : Fin 24) : Prop :=
  i = 14 ∨ i = 13 ∨ i = 10 ∨ i = 8 ∨ i = 22 ∨ i = 23

instance : DecidablePred generatedTenthE7StandardOutside := fun i =>
  inferInstanceAs (Decidable (i = 14 ∨ i = 13 ∨ i = 10 ∨ i = 8 ∨ i = 22 ∨ i = 23))

/-- The complete outside support is exactly the outside part of the actual companion code. -/
theorem generatedTenth_e7_standard_outside_code (i : Fin 24) :
    generatedTenthE7StandardOutside i ↔
      ¬ i.val < 8 ∧ golayEncoder (golayLabelCoefficients 110) i = 1 := by
  rw [generatedTenth_e7_standard_companion_coordinate]
  fin_cases i <;> norm_num [generatedTenthE7StandardOutside]

/-- All six original ordered source coordinates belong to the entire actual support. -/
theorem generatedTenth_e7_standard_outside_coordinates : ∀ i : Fin 6,
    generatedTenthE7StandardOutside (generatedTenthE7StandardOutsideCoordinates i) := by
  decide +kernel

/-- The ordered source coordinates as actual points of the full support. -/
def generatedTenthE7StandardOutsidePoint (i : Fin 6) :
    {j : Fin 24 // generatedTenthE7StandardOutside j} :=
  ⟨generatedTenthE7StandardOutsideCoordinates i,
    generatedTenth_e7_standard_outside_coordinates i⟩

/-- The actual six source coordinates enumerate the entire outside support exactly. -/
theorem generatedTenth_e7_standard_outside_point_bijective :
    Function.Bijective generatedTenthE7StandardOutsidePoint := by
  decide +kernel

/-- Exact source enumeration of the whole original outside support. -/
def generatedTenthE7StandardOutsideEquiv :
    Fin 6 ≃ {j : Fin 24 // generatedTenthE7StandardOutside j} :=
  Equiv.ofBijective generatedTenthE7StandardOutsidePoint
    generatedTenth_e7_standard_outside_point_bijective

/-- The actual whole flag group fixes every coordinate of its complete companion code. -/
theorem generatedTenth_e7_standard_flag_code_coordinate
    (p : generatedTenthE7StandardFlagPermutationGroup) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients 110) (p.val.val.val i) =
      golayEncoder (golayLabelCoefficients 110) i := by
  have hl : golayLabelPermutation p.val.val 110 = 110 := congrArg Prod.snd p.property
  have h := golayLabelPermutation_coordinate p.val.val 110 i
  rw [hl] at h
  exact h

/-- Every member of the entire flag group preserves all outside-support memberships. -/
theorem generatedTenth_e7_standard_flag_outside
    (p : generatedTenthE7StandardFlagPermutationGroup) (i : Fin 24) :
    generatedTenthE7StandardOutside (p.val.val.val i) ↔
      generatedTenthE7StandardOutside i := by
  rw [generatedTenth_e7_standard_outside_code, generatedTenth_e7_standard_outside_code,
    generatedTenth_e7_octad_point_membership p.val,
    generatedTenth_e7_standard_flag_code_coordinate]

/-- The genuine permutation restricted to all six actual ordered outside coordinates. -/
def generatedTenthE7StandardOutsidePermutation
    (p : generatedTenthE7StandardFlagPermutationGroup) : Equiv.Perm (Fin 6) :=
  generatedTenthE7StandardOutsideEquiv.trans
    ((p.val.val.val.subtypeEquiv
      (fun i => (generatedTenth_e7_standard_flag_outside p i).symm)).trans
        generatedTenthE7StandardOutsideEquiv.symm)

/-- Every coordinate of the restricted action is the original full permutation action. -/
theorem generatedTenth_e7_standard_outside_permutation_coordinate
    (p : generatedTenthE7StandardFlagPermutationGroup) (i : Fin 6) :
    generatedTenthE7StandardOutsideCoordinates (generatedTenthE7StandardOutsidePermutation p i) =
      p.val.val.val (generatedTenthE7StandardOutsideCoordinates i) := by
  have h := generatedTenthE7StandardOutsideEquiv.apply_symm_apply
    ((p.val.val.val.subtypeEquiv
      (fun j => (generatedTenth_e7_standard_flag_outside p j).symm))
        (generatedTenthE7StandardOutsideEquiv i))
  exact congrArg Subtype.val h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
