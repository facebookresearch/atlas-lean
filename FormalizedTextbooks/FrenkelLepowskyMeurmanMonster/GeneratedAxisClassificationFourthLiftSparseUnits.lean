/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerOperators

/-! Exact coordinate-unit expansion of the actual twenty-eight signed affine states. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The four literal coefficient labels are distinct actual spin addresses. -/
theorem generatedFourth_lift_plane_labels_injective : Function.Injective
    (fun s : Fin 4 => golayLabelCoefficients (generatedFourthLiftPlaneLabels s)) := by
  decide +kernel

/-- The explicit four addresses exhaust the actual common affine plane. -/
theorem generatedFourth_lift_plane_labels (t : SpinIndex) :
    generatedFourthLiftPlane t ↔
      ∃ s : Fin 4, t = golayLabelCoefficients (generatedFourthLiftPlaneLabels s) := by
  have hz : golayLabelCoefficients 0 = (0 : SpinIndex) := by decide +kernel
  have ha : golayLabelCoefficients 2062 =
      golayLabelCoefficients 14 + golayLabelCoefficients 2048 := by decide +kernel
  simp only [generatedFourthLiftPlane]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, by simpa only [generatedFourthLiftPlaneLabels, Matrix.cons_val_zero, hz] using h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h.trans ha.symm⟩
  · rintro ⟨s, h⟩
    fin_cases s <;> simp_all [generatedFourthLiftPlaneLabels]

/-- A binary spin address cancels itself under addition. -/
theorem generatedFourth_lift_add_self (a : SpinIndex) : a + a = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (a i)

/-- The signed common-plane function is exactly a four-unit expansion. -/
theorem generatedFourth_lift_plane_sum (a b : SpinIndex) (c : ZMod 2) (t : SpinIndex) :
    (∑ s : Fin 4,
      if t = a + golayLabelCoefficients (generatedFourthLiftPlaneLabels s) then
        generatedFourthLiftIntSign
          (c + spinDot b (golayLabelCoefficients (generatedFourthLiftPlaneLabels s))) else 0) =
      if generatedFourthLiftPlane (t + a) then
        generatedFourthLiftIntSign (c + spinDot b (t + a)) else 0 := by
  classical
  have he (s : Fin 4) : t = a + golayLabelCoefficients (generatedFourthLiftPlaneLabels s) ↔
      t + a = golayLabelCoefficients (generatedFourthLiftPlaneLabels s) := by
    constructor
    · intro h
      rw [h, add_right_comm, generatedFourth_lift_add_self, zero_add]
    · intro h
      calc
        t = (t + a) + a := by rw [add_assoc, generatedFourth_lift_add_self, add_zero]
        _ = golayLabelCoefficients (generatedFourthLiftPlaneLabels s) + a := by rw [h]
        _ = a + golayLabelCoefficients (generatedFourthLiftPlaneLabels s) := add_comm _ _
  simp_rw [he]
  by_cases h : generatedFourthLiftPlane (t + a)
  · rw [ite_eq_left h]
    obtain ⟨s, hs⟩ := (generatedFourth_lift_plane_labels _).mp h
    rw [Finset.sum_eq_single s]
    · simp only [hs, ite_true]
    · intro r _ hr
      have hn : t + a ≠ golayLabelCoefficients (generatedFourthLiftPlaneLabels r) := by
        intro hh
        exact hr (generatedFourth_lift_plane_labels_injective (hh.symm.trans hs))
      simp only [hn, ite_false]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro s _
    have hn : t + a ≠ golayLabelCoefficients (generatedFourthLiftPlaneLabels s) := by
      intro hh
      exact h ((generatedFourth_lift_plane_labels _).mpr ⟨s, hh⟩)
    simp only [hn, ite_false]

/-- Original signed integer weight of an actual family and an actual plane point. -/
def generatedFourthLiftUnitWeight (k : Fin 28) (s : Fin 4) : ℤ :=
  generatedFourthLiftIntSign (generatedFourthQAffineTensorScalePhases k +
    spinDot (generatedAxisFourthQAffineParameterCharacters
      (generatedFourthQAffineTensorFamilyIndex k))
      (golayLabelCoefficients (generatedFourthLiftPlaneLabels s)))

/-- Every actual tensor column is the exact finite sum of its original signed coordinate units. -/
theorem generatedFourth_lift_tensor_units (i : Fin 24) :
    (fun t => (griessConwayEncode generatedFourthAxis).2.2 t i) =
      ∑ k : Fin 28, ∑ s : Fin 4,
        (if i = generatedFourthQAffineTensorColumns k then
          (generatedFourthLiftUnitWeight k s : ℝ) / Real.sqrt 2 else 0) •
            (Pi.single (generatedFourthLiftSupportAddress k s) 1 : SpinSpace) := by
  classical
  funext t
  rw [generatedFourth_lift_integer_tensor]
  simp only [generatedFourthLiftIntegerTensor, Int.cast_sum, Finset.sum_div,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i = generatedFourthQAffineTensorColumns k
  · simp only [h, ite_true, generatedFourthLiftUnitWeight, Pi.single_apply,
      generatedFourthLiftSupportAddress]
    have hp := generatedFourth_lift_plane_sum
      (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k))
      (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex k))
      (generatedFourthQAffineTensorScalePhases k) t
    have hc := congrArg (fun z : ℤ => (z : ℝ) / Real.sqrt 2) hp
    simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_div] at hc
    simp only [Int.cast_ite, Int.cast_zero]
    rw [← hc]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  · simp only [h, ite_false, Int.cast_zero, zero_div, zero_mul, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
