/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.BelyiPolynomials
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Polynomial

/-- `√2` is algebraic over `ℚ`, as a root of `X ^ 2 - 2`. -/
theorem MathlibExtTest.isAlgebraic_sqrt_two : IsAlgebraic ℚ (Real.sqrt 2) :=
  ⟨X ^ 2 - C 2, X_pow_sub_C_ne_zero (by norm_num) 2, by
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]⟩

/-- Lemma 3.5 for `S = {√2} ⊆ ℝ`. -/
example : ∃ p : ℚ[X], 0 < p.natDegree ∧
    (∀ s ∈ ({Real.sqrt 2} : Set ℝ), aeval s p ∈ Set.range (algebraMap ℚ ℝ)) ∧
    ∀ r : ℝ, aeval r (derivative p) = 0 → aeval r p ∈ Set.range (algebraMap ℚ ℝ) :=
  exists_natDegree_pos_aeval_mem_range_of_isAlgebraic _ (Set.finite_singleton _)
    (by simpa using MathlibExtTest.isAlgebraic_sqrt_two)

/-- Lemma 3.5 for `S = {√2} ⊆ Q̄`, with `√2` a square root of `2` in `Q̄`. -/
example : ∃ s : AlgebraicClosure ℚ, s ^ 2 = 2 ∧ ∃ p : ℚ[X], 0 < p.natDegree ∧
    aeval s p ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) ∧
    ∀ r : AlgebraicClosure ℚ, aeval r (derivative p) = 0 →
      aeval r p ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure ℚ) two_pos
  obtain ⟨p, hp, hpS, hpC⟩ :=
    exists_natDegree_pos_aeval_mem_range_algebraicClosure {s} (Set.finite_singleton s)
  exact ⟨s, hs, p, hp, hpS s rfl, hpC⟩

/-- A concrete witness for `S = {√2} ⊆ ℝ`: `p = X ^ 2` has `p (√2) = 2`, and its derivative
`2 X` vanishes only at `0`, where `p` is `0`. -/
example : 0 < (X ^ 2 : ℚ[X]).natDegree ∧
    aeval (Real.sqrt 2) (X ^ 2 : ℚ[X]) ∈ Set.range (algebraMap ℚ ℝ) ∧
    ∀ r : ℝ, aeval r (derivative (X ^ 2 : ℚ[X])) = 0 →
      aeval r (X ^ 2 : ℚ[X]) ∈ Set.range (algebraMap ℚ ℝ) := by
  refine ⟨by simp, ⟨2, by simp [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]⟩, ?_⟩
  intro r hr
  have hr0 : r = 0 := by simpa using hr
  exact ⟨0, by simp [hr0]⟩

/-- The case `m = n = 1`: `c = 4` and `q₁ = 4 z (1 - z)`. -/
example : belyiPolynomial 1 1 = C 4 * X * (1 - X) := by
  norm_num [belyiPolynomial]

/-- The case `m = n = 1`: `q₁ (1 / 2) = 1`. -/
example : (belyiPolynomial 1 1).eval (1 / 2) = 1 := by
  have h := belyiPolynomial_eval_div 1 1 one_pos one_pos
  norm_num at h ⊢
  exact h

/-- The case `m = 2`, `n = 1`: `c = 27 / 4` and `q₁' = -(27/4) z (3 z - 2)`. -/
example : derivative (belyiPolynomial 2 1) =
    -C (27 / 4 : ℚ) * X ^ 1 * (1 - X) ^ 0 * (C 3 * X - C 2) := by
  rw [derivative_belyiPolynomial 2 1 (by norm_num) (by norm_num)]
  norm_num

/-- The zeros of `q₁'` for `m = 2`, `n = 1` lie in `{0, 1, 2 / 3}`. -/
example {r : ℝ} (hr : aeval r (derivative (belyiPolynomial 2 1)) = 0) :
    r = 0 ∨ r = 1 ∨ r = algebraMap ℚ ℝ (2 / 3) := by
  have h := eq_of_aeval_derivative_belyiPolynomial_eq_zero 2 1 (by norm_num) (by norm_num) hr
  norm_num at h ⊢
  exact h

/-- Boundary: for `m = 0` the value at `0` is `c = 1`, not `0`, so `belyiPolynomial_eval_zero`
needs `0 < m`. -/
example : (belyiPolynomial 0 1).eval 0 = 1 := by
  norm_num [belyiPolynomial]
