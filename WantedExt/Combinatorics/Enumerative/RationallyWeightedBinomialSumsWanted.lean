/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber
public import MathlibExt.Combinatorics.Enumerative.PolynomiallyWeightedFibonacciSums
public import MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums
public import MathlibExt.Combinatorics.Enumerative.RisingFactorialAntiderivatives
public import MathlibExt.Combinatorics.Enumerative.ScherkRisingFactorials
public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Rationally weighted binomial sums via differential and integral operators

Statements from Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation
of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), no. 1, 45–56.

`{r, i}` is `Nat.stirlingSecond r i`, `(N)_i` is the falling factorial `N.descFactorial i`, and the
rising factorial `(k + 1)^{(s)} = (k + 1)(k + 2) ⋯ (k + s)` is `(k + 1).ascFactorial s`. A
polynomial `f(x) = ∑_{k=0}^N a_k x^k` is written `∑ k ∈ range (N + 1), C (a k) * X ^ k`, and its
`i`-th derivative is `derivative^[i]`. `F_n` and `L_n` are `Nat.fib n` and `lucasNumber n`.

Epsteen's identity (`sum_choose_div_succ`), Finkel's identity
(`sum_neg_one_pow_choose_div_eq_harmonic`), and the inverse-square identity
(`sum_choose_mul_pow_div_sq`) are proved in
`MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Stirling numbers of the second kind with three blocks.** For every integer $r \ge 1$, the
Stirling number of the second kind $S(r, 3)$ satisfies
$S(r, 3) = \frac{3^{r-1} + 1}{2} - 2^{r-1}$.

The source states this for $r \ge 3$; both sides vanish at $r = 1$ and $r = 2$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Proposition 2.2. -/
public theorem stirlingSecond_three_eq (r : ℕ) (hr : 1 ≤ r) :
    (Nat.stirlingSecond r 3 : ℚ) = (3 ^ (r - 1) + 1) / 2 - 2 ^ (r - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := stirlingSecond_mul_factorial_eq_sum (1 + m) 3
  simp [Finset.sum_range_succ, Nat.factorial, pow_add] at h
  have hR : ((Nat.stirlingSecond (1 + m) 3 : ℚ) : ℝ) = (((3 ^ m + 1) / 2 - 2 ^ m : ℚ) : ℝ) := by
    push_cast
    linear_combination h / 6
  rw [Nat.add_sub_cancel_left]
  exact_mod_cast hR

end

end MetaMathlibExt
