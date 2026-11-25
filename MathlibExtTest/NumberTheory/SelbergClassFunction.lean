/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SelbergClassFunction

/-! # Tests for `MathlibExt.NumberTheory.SelbergClassFunction` -/

namespace MathlibExtTest.NumberTheory.SelbergClassFunction

open MetaMathlibExt

/-- The constant function $1$, as a function in the Selberg class: its Dirichlet
coefficients are $a(1) = 1$ and $a(n) = 0$ for $n \ne 1$, it has no Gamma factors,
conductor $1$ and root number $1$. -/
private noncomputable def oneFunction : SelbergClassFunction where
  coeff := LSeries.delta
  toFun := fun _ ↦ 1
  coeff_one := by simp [LSeries.delta]
  lseries := by
    intro s _
    have hHas : HasSum (fun n : ℕ ↦ if n = 1 then (1 : ℂ) else 0) 1 :=
      hasSum_ite_eq 1 1
    have hfun : LSeries.term LSeries.delta s =
        fun n : ℕ ↦ if n = 1 then (1 : ℂ) else 0 := funext (LSeries.term_delta s)
    refine ⟨?_, ?_⟩
    · have h2 : HasSum (LSeries.term LSeries.delta s) 1 := by
        rw [hfun]
        exact hHas
      exact h2.summable
    · show ∑' n, LSeries.term LSeries.delta s n = 1
      rw [hfun]
      exact hHas.tsum_eq
  ramanujan := by
    intro ε _
    refine ⟨1, fun n ↦ ?_⟩
    by_cases hn : n = 1
    · simp [hn, LSeries.delta]
    · have h0 : LSeries.delta n = 0 := by simp [LSeries.delta, hn]
      rw [h0]
      simp only [norm_zero]
      positivity
  eulerProduct := by
    refine ⟨0, fun n hb ↦ by simp at hb, ⟨0, by norm_num, 0, fun n ↦ by simp⟩,
      0, fun s _ ↦ ⟨by simp, by simp⟩⟩
  analyticContinuation := by
    refine ⟨0, fun _ ↦ 1, differentiable_const 1, ⟨0, 1, fun s ↦ ?_⟩,
      fun s _ ↦ by simp⟩
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h1]
    calc (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      _ = 1 * Real.exp (‖s‖ ^ (0 : ℝ)) := by simp
  r := 0
  Q := 1
  Q_pos := one_pos
  lam := fun j ↦ j.elim0
  lam_pos := fun j ↦ j.elim0
  mu := fun j ↦ j.elim0
  mu_re_nonneg := fun j ↦ j.elim0
  omega := 1
  norm_omega := by simp
  functionalEquation := by
    intro s _ _ _
    simp

private example : oneFunction.coeff 1 = 1 := by simp [oneFunction, LSeries.delta]

private example : oneFunction.coeff 2 = 0 := by simp [oneFunction, LSeries.delta]

/-- For the constant function $1$, there is no nonzero Dirichlet coefficient with
index at least $2$: this is the excluded case of the no-$a$-points lemma. -/
private theorem oneFunction_no_coeff_ge_two :
    ¬∃ n, 2 ≤ n ∧ oneFunction.coeff n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  have h0 : LSeries.delta n = 0 := by simp [LSeries.delta, show n ≠ 1 by omega]
  exact hne (by simpa [oneFunction] using h0)

/-- The no-$a$-points lemma applied to the constant function $1$ and a nonzero $a$. -/
private theorem exists_no_aPoint_right_one (a : ℂ) (ha : a ≠ 0) :
    ∃ E₁ : ℝ, 1 ≤ E₁ ∧
      ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv 1 oneFunction.toFun s ≠ a :=
  oneFunction.exists_no_aPoint_right 1 le_rfl a (Or.inl ha)

end MathlibExtTest.NumberTheory.SelbergClassFunction
