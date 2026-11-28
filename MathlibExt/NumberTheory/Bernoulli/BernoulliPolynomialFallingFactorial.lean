/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Polynomial.Pochhammer
import all MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic

/-!
# Bernoulli polynomials in the falling-factorial basis

For every natural number `n`, the rational Bernoulli polynomial, with `B₁ = -1/2`,
is its constant term plus a sum of falling factorials with coefficients given by
Stirling numbers of the second kind. For positive `n` the proof recovers the nonconstant
part from an existing formula for the discrete antiderivative of `X^(n - 1)`.

## References

* Bakir Farhi, *Formulas Involving Bernoulli and Stirling Numbers of Both Kinds*,
  Journal of Integer Sequences 28 (2025), Article 25.2.6, pp. 1–16, Theorem 1.
* Hans Rademacher, *Topics in Analytic Number Theory*, Grundlehren der mathematischen
  Wissenschaften 169, Springer-Verlag, 1973, Chapter 1, §2, pp. 4–6, Formula (2.2),
  cited by Farhi for the falling-factorial expression.
* `MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic`: the proof uses `powerSumPoly` and
  `powerSumPoly_eq` in the namespace `MetaMathlibExt.sum_stirling_harmonic_eq_bernoulli`.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open Polynomial (C)
open MetaMathlibExt.sum_stirling_harmonic_eq_bernoulli (powerSumPoly powerSumPoly_eq)

/-- **Bernoulli polynomials in the falling-factorial basis.** Let $B_m$ be the Bernoulli numbers
(with $B_1 = -1/2$), $B_n(X) = \sum_{i=0}^{n} \binom{n}{i} B_i X^{n-i}$ the Bernoulli
polynomials over $\mathbb{Q}$, $S(m, j)$ the Stirling numbers of the second kind and
$X^{\underline{k}} = X(X-1)\cdots(X-k+1)$ the falling factorial. For every natural number
$n$, in $\mathbb{Q}[X]$,
$$B_n(X) = B_n + \sum_{k=1}^{n} \frac{n}{k} \, S(n-1, k-1) \, X^{\underline{k}}.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 1. -/
public theorem bernoulli_poly_eq (n : ℕ) :
    Polynomial.bernoulli n =
      Polynomial.C (bernoulli n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (Nat.stirlingSecond (n - 1) (k - 1) : ℚ)) *
          descPochhammer ℚ k := by
  cases n with
  | zero => simp
  | succ n =>
    calc
      Polynomial.bernoulli (n + 1) =
          C (bernoulli (n + 1)) + C ((n : ℚ) + 1) * powerSumPoly n := by
        rw [powerSumPoly_eq, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (by positivity),
          map_one, one_mul, add_comm (C (bernoulli (n + 1))), sub_add_cancel]
      _ = _ := by
        congr 1
        rw [powerSumPoly, Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc,
          Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_right, Nat.one_add, Nat.succ_sub_one, Nat.cast_succ]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul]
        congr 2
        ring

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
