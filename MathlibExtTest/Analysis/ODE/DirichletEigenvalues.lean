/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.DirichletEigenvalues
import Mathlib.Tactic.IntervalCases

/-! # Tests for `MathlibExt.Analysis.ODE.DirichletEigenvalues` -/

namespace MathlibExtTest.Analysis.ODE.DirichletEigenvalues

open Set MathlibExt.Analysis.DirichletEigenvaluesWanted.Analysis.ODE
open scoped Real

/-- The left side of `dirichlet_eigenvalues_eq_nat_sq`: `λ` is a Dirichlet eigenvalue of
`-y'' = λ y` on `[0, π]`. -/
private abbrev IsEigenvalue (lam : ℝ) : Prop :=
  ∃ (y : ℝ → ℝ) (J : Set ℝ),
    IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
    (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
    (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
    y 0 = 0 ∧ y Real.pi = 0 ∧
    ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0

-- Test section: the "if" direction. The smallest eigenvalue is `1 = 1 ^ 2`, and `4 = 2 ^ 2` is
-- the next one.
example : IsEigenvalue 1 := (dirichlet_eigenvalues_eq_nat_sq 1).2 ⟨1, one_pos, by norm_num⟩

example : IsEigenvalue 4 := (dirichlet_eigenvalues_eq_nat_sq 4).2 ⟨2, two_pos, by norm_num⟩

-- Test section: the "only if" direction. For `λ ≤ 0` (in particular `λ = 0`, where the
-- solutions are affine), every solution vanishing at `0` and `π` vanishes on `(0, π)`.
example {lam : ℝ} (hlam : lam ≤ 0) {y : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hJπ : Icc 0 π ⊆ J) (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy' : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) (h0 : y 0 = 0) (hπ : y π = 0) :
    ∀ x ∈ Ioo 0 π, y x = 0 := by
  by_contra! h
  obtain ⟨n, hn, rfl⟩ :=
    (dirichlet_eigenvalues_eq_nat_sq lam).1 ⟨y, J, hJ, hJπ, hy, hy', h0, hπ, h⟩
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

-- A positive real number that is not the square of an integer, such as `2`, is not an eigenvalue.
example : ¬ IsEigenvalue 2 := by
  intro h
  obtain ⟨n, -, hn⟩ := (dirichlet_eigenvalues_eq_nat_sq 2).1 h
  have hn' : n ^ 2 = 2 := by exact_mod_cast hn.symm
  have : n < 2 := by nlinarith
  interval_cases n <;> simp at hn'

-- The "only if" direction on a concrete function: `sin (√2 x)` solves `y'' = -2 y` on `ℝ`,
-- vanishes at `0` and equals `1` at `π / (2 √2) ∈ (0, π)`; since `2` is not the square of an
-- integer, it does not vanish at `π`.
example : Real.sin (√2 * π) ≠ 0 := by
  intro h
  have h2 : (0 : ℝ) < √2 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hd : ∀ x, HasDerivAt (fun x => Real.sin (√2 * x)) (Real.cos (√2 * x) * √2) x :=
    fun x => (hasDerivAt_const_mul (x := x) √2).sin
  have hderiv : deriv (fun x => Real.sin (√2 * x)) = fun x => Real.cos (√2 * x) * √2 :=
    funext fun x => (hd x).deriv
  have hlt : π / (2 * √2) < π := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num), Real.sqrt_one]
  have hval : Real.sin (√2 * (π / (2 * √2))) = 1 := by
    rw [show √2 * (π / (2 * √2)) = π / 2 by field_simp, Real.sin_pi_div_two]
  obtain ⟨n, -, hn⟩ := (dirichlet_eigenvalues_eq_nat_sq 2).1
    ⟨fun x => Real.sin (√2 * x), univ, isOpen_univ, subset_univ _,
      fun x _ => hderiv ▸ hd x,
      fun x _ => hderiv ▸ ((hasDerivAt_const_mul (x := x) √2).cos.mul_const √2).congr_deriv
        (by linear_combination -Real.sin (√2 * x) * hsq),
      by simp, h, π / (2 * √2), ⟨by positivity, hlt⟩, by simp [hval]⟩
  have hn' : n ^ 2 = 2 := by exact_mod_cast hn.symm
  have : n < 2 := by nlinarith
  interval_cases n <;> simp at hn'

end MathlibExtTest.Analysis.ODE.DirichletEigenvalues
