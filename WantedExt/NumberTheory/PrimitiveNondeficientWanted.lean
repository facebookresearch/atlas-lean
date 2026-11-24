/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Must a primitive non-deficient number always have a small component?

Statements from Joshua Zelinsky, "Must a Primitive Non-Deficient
Number Always Have a Small Component?", *Journal of Integer
Sequences* 29 (2026), Article 26.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.tex>).

Definitions follow the paper (TeX lines 88-92) and the encoding
already used by the MathlibExt proof of the paper's main theorem
(`MetaMathlibExt.primitive_nondeficient_prime_power_bound`):
`n` is *non-deficient* if `σ(n) ≥ 2n`, with `σ` spelled out as
`∑ d ∈ Nat.divisors n, d`, and *primitive* non-deficient if in
addition every proper divisor is deficient. The paper's
factorization `n = p₁^{a₁} ⋯ p_k^{a_k}` with
`p₁ < ⋯ < p_k` is encoded through `n.primeFactors` (so
`k = n.primeFactors.card`), `n.factorization p` for the
exponents, the radical `R = ∏ q ∈ n.primeFactors, q`, and explicit
extremal elements for `p₁` (least) and `p_k` (greatest). The
paper's abundancy `h(n) = σ(n)/n` is `abundancyIndex`, and its
supremum bound `H(n) = ∏_{p ∣ n} p/(p-1)` is `abundancySup`,
both in `ℚ`.

The paper's Theorem (label `maintheoremboundwithkR`: some
`p_i^{a_i+1} < 2kR`) is already proved in MathlibExt as
`MetaMathlibExt.primitive_nondeficient_prime_power_bound` and is
not restated; this module states the paper's remaining numbered
lemmas and propositions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientRadical
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientTwoPowMulPrime
public import MathlibExt.NumberTheory.OddTwoPrimeFactorsDeficient

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Small component for odd primitive non-deficient numbers with three or four prime factors.**
Let $n$ be an odd primitive non-deficient number with exactly $3$ or exactly $4$ distinct prime
factors, and let $R$ be the product of the distinct prime factors of $n$. Then some prime factor
$p$ of $n$ satisfies $p^{a+1} < 2R$, where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Checkforexactly3or4distinctprimefactors`). -/
theorem_wanted exists_pow_factorization_add_one_lt_two_mul_radical
    (n : ℕ) (hno : Odd n) (hn : IsPrimitiveNondeficient n)
    (hk : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * ∏ q ∈ n.primeFactors, q

/-- **Grün's bound for non-deficient numbers.** Let $n$ be a non-deficient number with $k$
distinct prime factors, the least of which is $p_1$. Then $\tfrac{3}{2} p_1 - 2 < k$, and if
$p_1 \ge 5$ then $p_1 + 2 \le k$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `Grun`). -/
theorem_wanted grun_bounds_of_isNondeficient
    (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) :
    (3 : ℚ) / 2 * (p₁ : ℚ) - 2 < (n.primeFactors.card : ℚ) ∧
      (5 ≤ p₁ → p₁ + 2 ≤ n.primeFactors.card)

/-- **Generalized Puchta lemma.** Let $n$ be a primitive non-deficient number with $k$ distinct
prime factors, the least of which is $p_1$, and suppose that $(p_1, k) \ne (3, 3)$. Let $\alpha$
be a rational number with $0 < \alpha < 1$ such that $H(n) \ge 2 + \alpha$, where
$H(n) = \prod_p p/(p-1)$ is the product over the distinct primes $p$ dividing $n$. Then some
prime factor $p$ of $n$ satisfies $p^{a+1} < \max\bigl(2(k + 2 + p_1)/\alpha,\ k(k+1)\bigr)$,
where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `GeneralizedPuchtalemma`). -/
theorem_wanted exists_pow_factorization_add_one_lt_max
    (n p₁ : ℕ) (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (hne : ¬ (p₁ = 3 ∧ n.primeFactors.card = 3))
    (α : ℚ) (hα0 : 0 < α) (hα1 : α < 1)
    (hH : 2 + α ≤ abundancySup n) :
    ∃ p ∈ n.primeFactors,
      ((p ^ (n.factorization p + 1) : ℕ) : ℚ) <
        max
          (2 * ((n.primeFactors.card : ℚ) + 2 + (p₁ : ℚ)) / α)
          ((n.primeFactors.card : ℚ) *
            ((n.primeFactors.card : ℚ) + 1))

/-- **Dichotomy for odd primitive non-deficient numbers.** Let $n$ be an odd primitive
non-deficient number, that is, a positive integer with $\sigma(n) \ge 2n$ all of whose proper
divisors $m$ satisfy $\sigma(m) < 2m$, where $\sigma$ is the sum of divisors. Let $k$ be the
number of distinct prime factors of $n$, let $p_1$ and $p_k$ be its least and greatest prime
factors, and let $R$ be the product of the distinct primes dividing $n$. Then either
$p_k < \sqrt{R}$, or some prime $p$ dividing $n$ satisfies $p^{a+1} < (k + 2 + p_1)(p_k - 1)$,
where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Proposition
(label `dichotomywithpk`). -/
theorem_wanted max_primeFactor_lt_sqrt_radical_or_exists_pow_lt
    (n p₁ pK : ℕ) (hno : Odd n)
    (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (hpK : pK ∈ n.primeFactors)
    (hmax : ∀ q ∈ n.primeFactors, q ≤ pK) :
    (pK : ℝ) < Real.sqrt ((∏ q ∈ n.primeFactors, q : ℕ) : ℝ) ∨
      ∃ p ∈ n.primeFactors,
        p ^ (n.factorization p + 1) <
          (n.primeFactors.card + 2 + p₁) * (pK - 1)

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
