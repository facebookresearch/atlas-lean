/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.PeriodicEntire

/-!
# Tests for Lemma 17.14 (periodic entire ⇒ constant, corrected form)

The main test is the counterexample to the book's printed one-sided
hypothesis: `f(s) = exp (2 * π * I * s)` is entire, `1`-periodic,
satisfies the one-sided bound `‖f s‖ ≤ exp (Im s)` for `Im s ≥ 0`,
and is not constant (`f 0 = 1`, `f (1 / 2) = -1`). The two-sided
hypothesis of the proved theorem already fails for it at `C = 1` and
`s = -I`, where `‖f (-I)‖ = exp (2 * π) > exp 1`.
-/

@[expose] public section

open Complex Filter Function Set
open scoped Real Topology

/-- The new theorem is available at the expected name and type. -/
example (f : ℂ → ℂ) (hf_diff : Differentiable ℂ f)
    (hf_per : Periodic f (1 : ℂ))
    (hf_growth : ∃ C : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      ‖f s‖ ≤ C * Real.exp |s.im|) :
    ∃ c : ℂ, f = Function.const ℂ c :=
  PeriodicEntire.eq_const_of_periodic_one_of_norm_le_exp_abs_im f hf_diff
    hf_per hf_growth

/-- A constant function satisfies the two-sided hypothesis, so the
theorem applies to it. -/
example : ∃ c : ℂ, (fun _ : ℂ => (5 : ℂ)) = Function.const ℂ c :=
  PeriodicEntire.eq_const_of_periodic_one_of_norm_le_exp_abs_im
    (fun _ : ℂ => (5 : ℂ)) (differentiable_const _)
    (fun _ => rfl)
    ⟨‖(5 : ℂ)‖, fun s _ _ => by
      calc ‖(5 : ℂ)‖ = ‖(5 : ℂ)‖ * 1 := (mul_one _).symm
        _ ≤ ‖(5 : ℂ)‖ * Real.exp |s.im| :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg _))
              (norm_nonneg _)⟩

/-- The counterexample function: `exp (2 * π * I * s)`. -/
private noncomputable def expTwoPiMulI (s : ℂ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I * s)

private lemma expTwoPiMulI_differentiable :
    Differentiable ℂ expTwoPiMulI := by
  unfold expTwoPiMulI
  exact Complex.differentiable_exp.comp
    ((differentiable_const _).mul differentiable_id)

private lemma expTwoPiMulI_periodic : Periodic expTwoPiMulI (1 : ℂ) := by
  intro s
  simp only [expTwoPiMulI]
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma expTwoPiMulI_norm (s : ℂ) :
    ‖expTwoPiMulI s‖ = Real.exp (-2 * Real.pi * s.im) := by
  simp only [expTwoPiMulI, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- The counterexample satisfies the book's one-sided bound for
`Im s ≥ 0`, since `‖f s‖ = exp (-2 * π * Im s) ≤ exp (Im s)`. -/
example : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 0 ≤ s.im →
    ‖expTwoPiMulI s‖ ≤ 1 * Real.exp s.im := by
  intro s _ _ h_im
  rw [one_mul, expTwoPiMulI_norm]
  apply Real.exp_le_exp_of_le
  nlinarith [Real.pi_pos, h_im]

/-- The counterexample is not constant: `f 0 = 1`, `f (1 / 2) = -1`. -/
example : ¬ ∃ c : ℂ, expTwoPiMulI = Function.const ℂ c := by
  rintro ⟨c, hc⟩
  have h0 : expTwoPiMulI 0 = 1 := by simp [expTwoPiMulI]
  have hhalf : expTwoPiMulI (1 / 2 : ℂ) = -1 := by
    simp only [expTwoPiMulI]
    have h1 : 2 * ↑Real.pi * I * (1 / 2 : ℂ) = ↑Real.pi * I := by ring
    rw [h1, Complex.exp_pi_mul_I]
  have h2 := congrFun hc 0
  have h3 := congrFun hc (1 / 2 : ℂ)
  rw [h0] at h2
  rw [hhalf] at h3
  simp only [Function.const_apply] at h2 h3
  rw [← h2] at h3
  exact (by norm_num : (-1 : ℂ) ≠ 1) h3

/-- The two-sided hypothesis already fails for the counterexample at
`C = 1` and `s = -I`: `‖f (-I)‖ = exp (2 * π) > exp 1`. -/
example : ¬ (∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
    ‖expTwoPiMulI s‖ ≤ 1 * Real.exp |s.im|) := by
  intro h
  have h1 := h (-I) (by simp) (by simp)
  rw [expTwoPiMulI_norm] at h1
  simp only [one_mul] at h1
  have h_im : (-I : ℂ).im = -1 := by simp
  rw [h_im, abs_neg, abs_one] at h1
  have h2 : Real.exp (1 : ℝ) < Real.exp (2 * Real.pi) :=
    Real.exp_strictMono (by nlinarith [Real.pi_gt_three])
  have h3 : -2 * Real.pi * (-1 : ℝ) = 2 * Real.pi := by ring
  rw [h3] at h1
  exact (not_le.mpr h2) h1

end
