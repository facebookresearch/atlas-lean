/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleSpinFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddMatrixFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The transported genuine odd-axis matrix fiber admits full-coordinate even Pauli corrections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equality of genuine physical matrices is preserved by every actual local action. -/
theorem generatedSeventh_local_matrix_congr (h : H) (x y : GriessSpace)
    (hxy : (griessConwayEncode x).1 = (griessConwayEncode y).1) :
    (griessConwayEncode (rhoLocal h x)).1 = (griessConwayEncode (rhoLocal h y)).1 := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  rw [← hf, generatedFourth_local_matrix, generatedFourth_local_matrix, hxy]

private theorem conjugated_axis_apply (a b : H) (x : GriessSpace) :
    rhoLocal (a⁻¹ * b * a) x =
      (rhoLocal a).symm (rhoLocal b (rhoLocal a x)) := by
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The original local middle matrix fiber has genuine full-axis Pauli phase corrections. -/
private theorem transported_middle_matrix_phase (f : localFiberSubgroup) (b : H)
    (hb : (griessConwayEncode (rhoLocal b
      (rhoLocal (localFiberIntoH f) generatedOddAxis))).1 =
        (griessConwayEncode
          (rhoLocal (localFiberIntoH f) generatedOddAxis)).1) :
    ∃ q : Q, rhoLocal (inclQ q)
      (rhoLocal b (rhoLocal (localFiberIntoH f) generatedOddAxis)) =
        rhoLocal (localFiberIntoH f) generatedOddAxis := by
  let a := localFiberIntoH f
  let k := a⁻¹ * b * a
  have hm : (griessConwayEncode (rhoLocal k generatedOddAxis)).1 =
      (griessConwayEncode generatedOddAxis).1 := by
    have h := generatedSeventh_local_matrix_congr a⁻¹ _ _ hb
    rw [map_inv] at h
    change (griessConwayEncode
      ((rhoLocal a).symm (rhoLocal b (rhoLocal a generatedOddAxis)))).1 = _ at h
    change (griessConwayEncode
      ((rhoLocal a).symm (rhoLocal b (rhoLocal a generatedOddAxis)))).1 =
        (griessConwayEncode ((rhoLocal a).symm (rhoLocal a generatedOddAxis))).1 at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [conjugated_axis_apply]
    exact h
  have hf : rhoLocal k generatedOddAxis ∈ generatedOddMatrixFiber := ⟨⟨k, rfl⟩, hm⟩
  rw [generatedOddMatrixFiber_eq_phase_orbit] at hf
  obtain ⟨r, hr⟩ := hf
  have hfix : rhoLocal (inclQ r⁻¹) (rhoLocal k generatedOddAxis) = generatedOddAxis := by
    rw [← hr, map_inv, map_inv]
    exact (rhoLocal (inclQ r)).symm_apply_apply _
  refine ⟨spinConjugation f.val.1 r⁻¹, ?_⟩
  have he : inclQ (spinConjugation f.val.1 r⁻¹) * b * a = a * inclQ r⁻¹ * k := by
    rw [inclQ_spinConjugation]
    change (a * inclQ r⁻¹ * a⁻¹) * b * a = a * inclQ r⁻¹ * (a⁻¹ * b * a)
    group
  have h := congrArg (fun g : H => rhoLocal g generatedOddAxis) he
  simp only [map_mul, LinearEquiv.mul_apply] at h
  exact h.trans (congrArg (rhoLocal a) hfix)

/-- The original local middle matrix fiber has genuine full-axis Pauli phase corrections. -/
theorem generatedSeventh_middle_matrix_phase (b : H)
    (hb : (griessConwayEncode (rhoLocal b
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis))).1 =
        (griessConwayEncode
          (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1) :
    ∃ q : Q, rhoLocal (inclQ q)
      (rhoLocal b (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) =
        rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis :=
  transported_middle_matrix_phase generatedSeventhLocalFiber b hb

/-- A genuine phase correction of the whole middle axis can be chosen with even modulation. -/
theorem generatedSeventh_middle_matrix_even_phase (b : H)
    (hb : (griessConwayEncode (rhoLocal b
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis))).1 =
        (griessConwayEncode
          (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1) :
    ∃ q : Q, spinModulation q 11 = 0 ∧ rhoLocal (inclQ q)
      (rhoLocal b (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) =
        rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis := by
  obtain ⟨q, hq⟩ := generatedSeventh_middle_matrix_phase b hb
  by_cases hm : spinModulation q 11 = 0
  · exact ⟨q, hm, hq⟩
  · have hm1 : spinModulation q 11 = 1 := by
      have h : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
      exact h _ hm
    let d := cocodeQ (golayLabelCoefficients 3079)
    have hd := generatedSeventh_middle_spin_fixed_axis d
      generatedSeventh_spin_state_odd_modulation_fixed
    refine ⟨d * q, ?_, ?_⟩
    · rw [spinModulation_mul]
      change spinModulation d 11 + spinModulation q 11 = 0
      rw [generatedSeventh_spin_odd_modulation_coordinates.2, hm1]
      decide
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, hq]
      exact hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
