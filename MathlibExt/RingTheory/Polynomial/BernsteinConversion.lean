/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/forseti-lean, commit
0a81edc7fe82748af7c9b1139229c4d898f50c28,
`Gimle/Forseti/BernsteinConversion.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Exact polynomial conversion to the Bernstein basis

Exact binomial weights express any monomial of degree at most `n` in the
Bernstein basis of degree `n`, at every real argument. Summing these weights
against a polynomial's coefficients gives an explicit conversion for every
polynomial of degree at most `n`, including degree elevation.

Mathematical reference: A. P. Smith, Enclosure Methods for Systems of Polynomial
Equations and Inequalities (2012), Section 3.1.3, Theorem 3.2, equation (3.9),
https://d-nb.info/1028327854/34. This is its univariate basis-conversion formula;
the identity is polynomial, so evaluation is not restricted to the unit interval.
-/
@[expose] public section
open Finset
namespace bernsteinPolynomial
/-- `∑ν C(ν,k) C(n,ν) sᵛ (1-s)ⁿ⁻ᵛ = C(n,k) sᵏ`, the monomial in Bernstein form. -/
theorem choose_bernstein_sum (n k : Nat) (hk : k ≤ n) (s : ℝ) :
    ∑ ν ∈ range (n + 1), (ν.choose k : ℝ) *
      (bernsteinPolynomial ℝ n ν).eval s = (n.choose k : ℝ) * s ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show k + m + 1 = k + (m + 1) by omega, sum_range_add]
  have low : ∑ ν ∈ range k, (ν.choose k : ℝ) * (bernsteinPolynomial ℝ (k + m) ν).eval s = 0 := by
    apply sum_eq_zero
    intro ν hν
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hν)]
    simp
  rw [low, zero_add]
  have term : ∀ j ∈ range (m + 1),
      ((k + j).choose k : ℝ) * (bernsteinPolynomial ℝ (k + m) (k + j)).eval s =
        ((k + m).choose k : ℝ) * s ^ k * (s ^ j * (1 - s) ^ (m - j) * (m.choose j : ℝ)) := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hc := Nat.choose_mul (n := k + m) (k := k + j) (s := k) (by omega)
    rw [show k + m - k = m by omega, show k + j - k = j by omega] at hc
    have hc' : ((k + m).choose (k + j) : ℝ) * ((k + j).choose k : ℝ) =
        ((k + m).choose k : ℝ) * (m.choose j : ℝ) := by exact_mod_cast hc
    simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, show k + m - (k + j) = m - j by omega, pow_add]
    linear_combination (s ^ k * s ^ j * (1 - s) ^ (m - j)) * hc'
  rw [sum_congr rfl term, ← mul_sum]
  have binom := (add_pow s (1 - s) m).symm
  rw [show s + (1 - s) = 1 by ring, one_pow] at binom
  rw [binom, mul_one]


/-- Monomial-to-Bernstein conversion, including degree zero and endpoints. -/
theorem monomial_bernstein (n k : ℕ) (hk : k ≤ n) (s : ℝ) :
    ∑ ν ∈ range (n + 1), ((ν.choose k : ℝ) / n.choose k) *
      (bernsteinPolynomial ℝ n ν).eval s = s ^ k := by
  have hc : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  simp_rw [div_mul_eq_mul_div, ← sum_div, choose_bernstein_sum n k hk s]
  exact mul_div_cancel_left₀ _ hc

/-- The coefficient at index `j` in the degree-`n` Bernstein expansion of `p`.
Reconstruction requires `p.natDegree ≤ n`. -/
noncomputable def bernsteinCoeff (n : ℕ) (p : Polynomial ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), p.coeff k * ((j.choose k : ℝ) / n.choose k)

/-- Exact conversion evaluated at any real argument, without an interval restriction. -/
theorem eval_eq_sum_bernstein {n : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ n) (s : ℝ) :
    p.eval s = ∑ j ∈ range (n + 1),
      bernsteinCoeff n p j * (bernsteinPolynomial ℝ n j).eval s := by
  calc
    p.eval s = ∑ k ∈ range (n + 1), p.coeff k * s ^ k := by
      have h := congrArg (Polynomial.eval s)
        (p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp))
      simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using h
    _ = ∑ k ∈ range (n + 1), p.coeff k *
        ∑ j ∈ range (n + 1), ((j.choose k : ℝ) / n.choose k) *
          (bernsteinPolynomial ℝ n j).eval s := by
      apply sum_congr rfl
      intro k hk
      rw [monomial_bernstein n k (Nat.le_of_lt_succ (mem_range.mp hk)) s]
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [bernsteinCoeff, sum_mul]
      apply sum_congr rfl
      intro k _
      ring

/-- Every polynomial of degree at most `n` has this explicit Bernstein expansion. -/
theorem eq_sum_bernstein {n : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ n) :
    p = ∑ j ∈ range (n + 1),
      Polynomial.C (bernsteinCoeff n p j) * bernsteinPolynomial ℝ n j := by
  apply Polynomial.funext
  intro s
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    using eval_eq_sum_bernstein hp s
end bernsteinPolynomial
