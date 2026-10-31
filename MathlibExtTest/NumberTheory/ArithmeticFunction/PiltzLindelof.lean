/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PiltzLindelof
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tests for the Piltz divisor problem
-/

@[expose] public section

open ArithmeticFunction

example : piltz 3 12 ≤ sigma 0 12 ^ 3 := piltz_le_sigma_zero_pow 3 12

example : ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, (piltz 3 n : ℝ) ≤ A * (n : ℝ) ^ (1 / 4 : ℝ) :=
  exists_piltz_le_mul_rpow 3 (by norm_num)

-- `k = 0`: `d_0 = δ`, whose L-series is `1 = ζ^0`.
example (s : ℂ) (hs : 1 < s.re) : LSeries (fun n : ℕ => (piltz 0 n : ℂ)) s = 1 := by
  simpa using LSeries_piltz 0 hs

-- `∑ d(n) / n² = ζ(2)² = π⁴ / 36`.
example : LSeries (fun n : ℕ => (piltz 2 n : ℂ)) 2 = (Real.pi : ℂ) ^ 4 / 36 := by
  rw [LSeries_piltz 2 (by norm_num), riemannZeta_two]
  ring

example : LSeriesSummable (fun n : ℕ => (piltz 5 n : ℂ)) 2 :=
  LSeriesSummable_piltz 5 (by norm_num)

/-! ### The main-term polynomial -/

-- `k = 1`: `∑_{n ≤ x} 1 = x + O(x ^ (1 / 2 + ε))`, so `P_0 = 1`.
example : piltzMainPoly 1 = 1 := by
  simp [piltzMainPoly, riemannZeta₁_one]

-- `k = 2`: Dirichlet's divisor problem, `P_1(y) = y + 2γ - 1`.
example :
    piltzMainPoly 2 = Polynomial.X + Polynomial.C (2 * Real.eulerMascheroniConstant - 1) := by
  have hd : HasDerivAt (fun s : ℂ => riemannZeta₁ s ^ 2 / s)
      (2 * (Real.eulerMascheroniConstant : ℂ) - 1) 1 := by
    have h := ((differentiable_riemannZeta₁ 1).hasDerivAt.fun_pow 2).div (hasDerivAt_id' 1)
      one_ne_zero
    rw [deriv_riemannZeta₁_one, riemannZeta₁_one] at h
    convert h using 1
    ring
  have h1 : iteratedDeriv 1 (fun s : ℂ => riemannZeta₁ s ^ 2 / s) 1
      = 2 * (Real.eulerMascheroniConstant : ℂ) - 1 := by
    rw [iteratedDeriv_one, hd.deriv]
  simp only [piltzMainPoly, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedDeriv_zero, riemannZeta₁_one, h1]
  norm_num

example (k : ℕ) (hk : 1 ≤ k) : (piltzMainPoly k).natDegree = k - 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some (piltzMainPoly_degree hk)

example : (piltzMainPoly 3).leadingCoeff = 1 / 2 := by
  rw [piltzMainPoly_leadingCoeff (by norm_num)]
  norm_num [Nat.factorial]

/-! ### The conditional asymptotic formula

The Lindelöf hypothesis is an open problem, so the theorem can only be used conditionally. -/

example (hLH : LindelofHypothesis) :
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz 2 n : ℝ))
        - x * (piltzMainPoly 2).eval (Real.log x)) =O[Filter.atTop]
      fun x : ℝ => x ^ (1 / 2 + 1 / 100 : ℝ) :=
  sum_piltz_sub_mul_piltzMainPoly_isBigO_of_lindelofHypothesis hLH (k := 2) (by norm_num)
    (by norm_num)

-- `P` does not depend on `ε`.
example (hLH : LindelofHypothesis) (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Polynomial ℝ, P.leadingCoeff = 1 / ((k - 1).factorial : ℝ) ∧ ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ))
        - x * P.eval (Real.log x)) =O[Filter.atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  obtain ⟨P, -, hP, h⟩ := exists_polynomial_sum_piltz_isBigO_of_lindelofHypothesis hLH hk
  exact ⟨P, hP, h⟩
