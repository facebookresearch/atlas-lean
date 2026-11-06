/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardNormalPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitProjection

/-! All complete actual signed flag candidates preserve the entire original E7 projector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every actual signed flag candidate commutes with the complete standard E7 projector. -/
theorem generatedTenth_e7_signed_flag_projection_commute
    (v : generatedTenthE7SignedFlagCandidates) (x : Fin 24 → ℝ) :
    (generatedTenthE7SignedFlagSpatial v).val
      (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
        (generatedTenthE7SignedFlagSpatial v).val x := by
  have hc : v.2.val.val 4 = v.2.val.val 5 := v.2.property.1
  have hpre8 (i : Fin 24) : (v.1.val.val.val.symm i).val < 8 ↔ i.val < 8 := by
    have h := generatedTenth_e7_octad_point_membership v.1.val (v.1.val.val.val.symm i)
    rw [v.1.val.val.val.apply_symm_apply] at h
    exact h.symm
  have hpre4 (i : Fin 24) : v.1.val.val.val.symm i = 4 ↔ i = v.1.val.val.val 4 :=
    v.1.val.val.val.symm_apply_eq
  have hpre5 (i : Fin 24) : v.1.val.val.val.symm i = 5 ↔ i = v.1.val.val.val 5 :=
    v.1.val.val.val.symm_apply_eq
  have ha4 := v.1.val.val.val.symm_apply_apply 4
  have ha5 := v.1.val.val.val.symm_apply_apply 5
  rcases generatedTenth_e7_standard_flag_normal_pair v.1 with ⟨h4, h5⟩ | ⟨h4, h5⟩
  all_goals
    simp only [h4, h5] at hpre4 hpre5 ha4 ha5
    funext i
    unfold generatedTenthE7SignedFlagSpatial
    rw [golayMonomialPair_apply, generatedTenth_e7_root_orbit_projector_coordinate,
      generatedTenth_e7_root_orbit_projector_coordinate]
    simp only [golayMonomialPair_apply, hpre8, hpre4, hpre5, ha4, ha5]
    by_cases hi4 : i = 4
    · subst i
      simp [hc]
      ring
    · by_cases hi5 : i = 5
      · subst i
        simp [hc]
        ring
      · by_cases hi8 : i.val < 8
        · simp only [hi4, hi5, hi8, false_or, ite_true, ite_false, sub_zero]
          ring
        · simp [hi4, hi5, hi8]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
