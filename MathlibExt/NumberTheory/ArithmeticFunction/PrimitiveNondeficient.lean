/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndex
import Mathlib.Tactic.Linarith

/-!
# Primitive non-deficient numbers

This file defines primitive non-deficient numbers and their abundancy quantities, and proves
Zelinsky's reciprocal estimate used to bound prime-power components.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Non-deficient number.** A natural number $n$ is non-deficient when $n \ne 0$ and
$\sigma(n) \ge 2n$, where $\sigma(n)$ is the sum of the positive divisors of $n$.

Positivity is part of the notion: $0$ has no divisors in this convention, so the inequality
alone would make $0$ non-deficient. -/
def IsNondeficient (n : ℕ) : Prop :=
  n ≠ 0 ∧ 2 * n ≤ ∑ d ∈ Nat.divisors n, d

/-- **Primitive non-deficient number.** A natural number $n$ is primitive non-deficient when it
is non-deficient and every proper divisor $m$ of $n$ (a divisor with $m < n$) is deficient, that
is, $\sigma(m) < 2m$, where $\sigma(m)$ is the sum of the positive divisors of $m$. -/
def IsPrimitiveNondeficient (n : ℕ) : Prop :=
  IsNondeficient n ∧
    ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m

/-- **Abundancy index.** For a natural number $n$, the abundancy index is the rational number
$h(n) = \sigma(n)/n$, where $\sigma(n)$ is the sum of the positive divisors of $n$.

At $n = 0$ this gives $h(0) = 0$, since division by zero is $0$ in $\mathbb{Q}$; the abundancy
index is only meaningful for positive $n$. -/
noncomputable def abundancyIndex (n : ℕ) : ℚ :=
  ((∑ d ∈ Nat.divisors n, d : ℕ) : ℚ) / (n : ℚ)

/-- The ATLAS abundancy index agrees with Mathlib's `Nat.abundancyIndex`. -/
lemma abundancyIndex_eq_nat_abundancyIndex (n : ℕ) : abundancyIndex n = n.abundancyIndex := rfl

/-- **Product of $p/(p-1)$ over the prime factors.** For a natural number $n$, let
$H(n) = \prod_p p/(p-1)$ in $\mathbb{Q}$, the product over the distinct primes $p$ dividing $n$.
For $n = 0$ the product is empty ($0$ is taken to have no prime factors), so $H(0) = 1$. -/
noncomputable def abundancySup (n : ℕ) : ℚ :=
  ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)

/-- **Zelinsky's reciprocal bound.** For real numbers $k$ and $m$ with $k \ge 2$ and
$0 < m < 1/(k(k+1))$, we have $1/(1 - km) < 1 + (k+1)m$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `KMlemma`). -/
theorem one_div_one_sub_mul_lt_add
    (k m : ℝ) (hk : 2 ≤ k) (hm0 : 0 < m)
    (hm : m < 1 / (k * (k + 1))) :
    1 / (1 - k * m) < 1 + (k + 1) * m := by
  have hk0 : 0 < k := by linarith
  have hbound : m * (k * (k + 1)) < 1 :=
    (lt_div_iff₀ (mul_pos hk0 (by linarith))).mp hm
  have hkm : k * m < 1 := by
    linarith only [hbound, mul_nonneg (sq_nonneg k) hm0.le]
  apply (div_lt_iff₀ (sub_pos.mpr hkm)).2
  linarith only [mul_pos hm0 (sub_pos.mpr hbound)]

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
