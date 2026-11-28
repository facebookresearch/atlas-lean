/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.IntegralFeedback

/-!
# Equilibrium and DC gain of a two-state integral-feedback loop

Åström and Murray, *Feedback Systems*, 2nd ed., §7.4, Eq. (7.26) and pp. 7-25–7-26,
give the integrator augmentation and its steady-state interpretation. The matrices and
calculations below are for the specific loop with output `e` and integrator state `z`.
No stability or convergence is asserted.
-/

public section

open Matrix
open MathlibExt.Biology.Dynamics.IntegralFeedback

namespace MathlibExt.Biology.Dynamics.IntegralFeedbackLoop

/-- For positive gains `a` and `b`, the loop `ė = -a * e - b * z + r`, `ż = e`, `y = e`
has the displayed two-state SISO realization. Its state matrix has determinant `b` and is
nonsingular. For each constant input `r` the unique equilibrium is `(0, r / b)`, with output
zero, and the DC gain `D - C A⁻¹ B` vanishes. -/
theorem integral_feedback_loop_equilibrium_and_dc_gain {a b : ℝ} (_ha : 0 < a) (hb : 0 < b) :
    let S : LinearSystem (Fin 2) := ⟨!![-a, -b; 1, 0], ![1, 0], ![1, 0], 0⟩
    (∀ (x : Fin 2 → ℝ) (r : ℝ), S.field x r 0 = -a * x 0 - b * x 1 + r ∧
      S.field x r 1 = x 0 ∧ S.output x r = x 0) ∧
    S.A.det = b ∧ IsUnit S.A.det ∧
    (∀ (x : Fin 2 → ℝ) (r : ℝ), S.field x r = 0 ↔ x = ![0, r / b]) ∧
    (∀ r : ℝ, S.output ![0, r / b] r = 0) ∧ S.dcGain = 0 := by
  intro S
  have field₀ (x : Fin 2 → ℝ) (r : ℝ) : S.field x r 0 = -a * x 0 - b * x 1 + r := by
    simp [S, LinearSystem.field, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]
  have field₁ (x : Fin 2 → ℝ) (r : ℝ) : S.field x r 1 = x 0 := by
    simp [S, LinearSystem.field, dotProduct, Fin.sum_univ_two]
  have output_eq (x : Fin 2 → ℝ) (r : ℝ) : S.output x r = x 0 := by
    simp [S, LinearSystem.output, dotProduct, Fin.sum_univ_two]
  have hdet : S.A.det = b := by simp [S, det_fin_two_of]
  have hunit : IsUnit S.A.det := hdet ▸ isUnit_iff_ne_zero.mpr hb.ne'
  have equilibrium (r : ℝ) : S.field ![0, r / b] r = 0 := by
    ext i
    fin_cases i
    · simp [field₀, mul_div_cancel₀ r hb.ne']
    · simp [field₁]
  have equilibrium_iff (x : Fin 2 → ℝ) (r : ℝ) : S.field x r = 0 ↔ x = ![0, r / b] := by
    have hpoint := (S.field_eq_zero_iff hunit _ r).mp (equilibrium r)
    rw [S.field_eq_zero_iff hunit, ← hpoint]
  have adaptation : S.HasPerfectAdaptation :=
    S.hasPerfectAdaptation_of_hasIntegralFeedback ⟨![0, 1], fun x r ↦ by
      simp [dotProduct, Fin.sum_univ_two, field₁, output_eq]⟩
  exact ⟨fun x r ↦ ⟨field₀ x r, field₁ x r, output_eq x r⟩, hdet, hunit, equilibrium_iff,
    fun r ↦ adaptation r _ (equilibrium r),
    (S.hasPerfectAdaptation_iff_dcGain_eq_zero hunit).mp adaptation⟩

end MathlibExt.Biology.Dynamics.IntegralFeedbackLoop
