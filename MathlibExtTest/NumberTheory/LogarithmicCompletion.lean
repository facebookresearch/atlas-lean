/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LogarithmicCompletion

/-! # Endpoint tests for completion of exponential sums -/

namespace MathlibExtTest.NumberTheory.LogarithmicCompletion

open Complex Finset Polynomial

private noncomputable def quadraticMax (p : ℕ) : ℝ :=
  ((range p).sup fun y : ℕ =>
    ‖∑ x ∈ Icc 1 p, exp (2 * Real.pi * I * ((x : ℂ) ^ 2 + y * x) / p)‖₊ : NNReal)

-- At the smallest prime and shortest length the incomplete sum has norm exactly one.
example : 1 < quadraticMax 5 * Real.log 5 := by
  have : Fact (1 < (5 : ℕ)) := ⟨by decide⟩
  have h := MetaMathlibExt.norm_incompleteSum_lt_sup_mul_log 5 (by decide) le_rfl
    (X ^ 2) (by simp) 1 le_rfl (by decide)
  simpa [quadraticMax, norm_exp] using h

-- The closed upper endpoint includes the representative of zero modulo the prime.
example : ‖∑ x ∈ Icc 1 (37 : ℕ), exp (2 * Real.pi * I * (x : ℂ) ^ 2 / 37)‖ <
    quadraticMax 37 * Real.log 37 := by
  have : Fact (1 < (37 : ℕ)) := ⟨by decide⟩
  have h := MetaMathlibExt.norm_incompleteSum_lt_sup_mul_log 37 (by decide) (by decide)
    (X ^ 2) (by simp) 37 (by decide) le_rfl
  simpa [quadraticMax] using h

private lemma exp_mod_two (t : ℕ) : exp (2 * Real.pi * I * (t : ℂ) / 2) = (-1 : ℂ) ^ t := by
  rw [show 2 * Real.pi * I * (t : ℂ) / 2 = (t : ℂ) * (Real.pi * I) by ring,
    exp_nat_mul, exp_pi_mul_I]

-- The nonzero twist gives a sharp error at the smallest prime and shortest interval.
example : ∃ θ : ℂ, ‖θ‖ = 1 ∧ (-1 : ℂ) = θ := by
  have h := MetaMathlibExt.exists_incompleteSum_eq_completeSum_add 2 (by decide) X 1
    le_rfl (by decide)
  have hIcc : Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hhalf : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hfour : exp (2 * Real.pi * I * 4 / 2) = 1 := by
    have h := exp_mod_two 4
    norm_num at h
    exact h
  obtain ⟨θ, _, hθ⟩ := h
  have hθ' : (-1 : ℂ) = θ := by
    norm_num [hIcc, exp_mod_two, hhalf, hfour] at hθ
    norm_num [mul_assoc] at hθ
    exact hθ
  exact ⟨θ, by rw [← hθ']; simp, hθ'⟩

-- At full length the sine weight vanishes, even when the nonzero twist has norm two.
example : ∃ θ : ℂ, ‖θ‖ ≤ 1 ∧ (0 : ℂ) = θ * 0 * 2 := by
  have h := MetaMathlibExt.exists_incompleteSum_eq_completeSum_add 2 (by decide) X 2
    (by decide) le_rfl
  have hIcc : Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hsin : Real.sin (Real.pi * 2 / 2) = 0 := by
    rw [show Real.pi * 2 / 2 = Real.pi by ring, Real.sin_pi]
  simpa [hIcc, exp_mod_two, hsin, Real.sin_pi_div_two] using h

end MathlibExtTest.NumberTheory.LogarithmicCompletion
