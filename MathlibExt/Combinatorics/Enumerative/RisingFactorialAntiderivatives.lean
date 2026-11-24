/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rising-factorial weighted sums via iterated antiderivatives

Integrating a polynomial repeatedly divides its coefficients by rising factorials.
For arbitrary antiderivatives, their values at zero determine the correction polynomial.
-/

namespace MetaMathlibExt

private theorem hasDerivAt_divided_monomial (c d x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ ↦ c * y ^ (n + 1) / (↑(n + 1) * d))
      (c * x ^ n / d) x := by
  have hn : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
  simpa only [Nat.add_one_sub_one, mul_left_comm c (↑(n + 1) : ℝ), mul_div_mul_left _ _ hn]
    using ((hasDerivAt_pow (n + 1) x).const_mul c).div_const (↑(n + 1) * d)

/-- **Rising-factorial weighted sums via iterated antiderivatives.** Let $N$ and $s$ be natural
numbers, $a_0, \dots, a_N$ real numbers and $f(y) = \sum_{k=0}^{N} a_k y^k$. Let
$I_0, I_1, I_2, \dots$ be functions $\mathbb{R} \to \mathbb{R}$ with $I_0 = f$ such that for every
$j \ge 0$ the function $I_{j+1}$ is differentiable on $\mathbb{R}$ with derivative $I_j$ (the
constants of integration are arbitrary). Write $m^{(i)} = m(m+1)\cdots(m+i-1)$ for the rising
factorial. Then for every real number $x$,

$$\sum_{k=0}^{N} \frac{a_k\, x^{k+s}}{(k+1)^{(s)}} =
I_s(x) - \sum_{j=1}^{s} \frac{I_j(0)\, x^{s-j}}{(s-j)!}.$$

The source assumes $s > 0$; for $s = 0$ the identity reads $f(x) = I_0(x)$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.2). -/
public theorem sum_coeff_mul_pow_div_ascFactorial_eq_antideriv (a : ℕ → ℝ) (N s : ℕ)
    (I : ℕ → ℝ → ℝ) (hI0 : ∀ y, I 0 y = ∑ k ∈ Finset.range (N + 1), a k * y ^ k)
    (hI : ∀ j y, HasDerivAt (I (j + 1)) (I j y) y) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), a k * x ^ (k + s) / (k + 1).ascFactorial s =
      I s x - ∑ j ∈ Finset.Icc 1 s, I j 0 * x ^ (s - j) / (s - j).factorial := by
  let weighted (r : ℕ) (y : ℝ) :=
    ∑ k ∈ Finset.range (N + 1), a k * y ^ (k + r) / (k + 1).ascFactorial r
  let correction (r : ℕ) (y : ℝ) :=
    ∑ j ∈ Finset.Icc 1 r, I j 0 * y ^ (r - j) / (r - j).factorial
  suffices h : (fun y ↦ weighted s y + correction s y) = I s from
    eq_sub_iff_add_eq.mpr (congrFun h x)
  induction s with
  | zero =>
    funext y
    simp [weighted, correction, hI0]
  | succ s ih =>
    -- Split off the new integration constant. All remaining powers are positive.
    have step (y : ℝ) : correction (s + 1) y =
        (∑ j ∈ Finset.Icc 1 s, I j 0 * y ^ (s - j + 1) / (s - j + 1).factorial) +
          I (s + 1) 0 := by
      dsimp only [correction]
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le s))]
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.succ_sub (Finset.mem_Icc.mp hj).2]
    have hderiv (y : ℝ) :
        HasDerivAt (fun z ↦ weighted (s + 1) z + correction (s + 1) z) (I s y) y := by
      rw [← ih]
      apply HasDerivAt.add
      · apply HasDerivAt.fun_sum
        intro k _
        simpa only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.add_right_comm k 1 s, Nat.add_assoc]
          using hasDerivAt_divided_monomial (a k) ((k + 1).ascFactorial s) y (k + s)
      · rw [funext step]
        apply HasDerivAt.add_const
        apply HasDerivAt.fun_sum
        intro j _
        simpa only [Nat.factorial_succ, Nat.cast_mul] using
          hasDerivAt_divided_monomial (I j 0) (s - j).factorial y (s - j)
    apply eq_of_fderiv_eq (fun y ↦ (hderiv y).differentiableAt)
      (fun y ↦ (hI s y).differentiableAt)
      (fun y ↦ (hderiv y).hasFDerivAt.fderiv.trans (hI s y).hasFDerivAt.fderiv.symm) 0
    simp [weighted, step]

end MetaMathlibExt
