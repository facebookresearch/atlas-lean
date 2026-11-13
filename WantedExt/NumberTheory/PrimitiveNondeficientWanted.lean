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

set_option autoImplicit false

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

/-- **Product of $p/(p-1)$ over the prime factors.** For a natural number $n$, let
$H(n) = \prod_p p/(p-1)$ in $\mathbb{Q}$, the product over the distinct primes $p$ dividing $n$.
For $n = 0$ the product is empty ($0$ is taken to have no prime factors), so $H(0) = 1$. -/
noncomputable def abundancySup (n : ℕ) : ℚ :=
  ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)

/-- **Even primitive non-deficient numbers with two prime factors.** Let $p$ be an odd prime and
$a$ a natural number. Then $2^a p$ is primitive non-deficient if and only if
$2^a < p \le 2^{a+1} - 1$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), first
part. -/
theorem_wanted isPrimitiveNondeficient_two_pow_mul_prime_iff
    (a p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) :
    IsPrimitiveNondeficient (2 ^ a * p) ↔
      2 ^ a < p ∧ p ≤ 2 ^ (a + 1) - 1

/-- **Odd numbers with two prime factors are deficient.** If $n$ is an odd natural number with
exactly two distinct prime divisors, then $\sigma(n) < 2n$, where $\sigma(n)$ is the sum of the
positive divisors of $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), second
part. -/
theorem_wanted deficient_of_odd_card_primeFactors_eq_two
    (n : ℕ) (hno : Odd n) (hk : n.primeFactors.card = 2) :
    ∑ d ∈ Nat.divisors n, d < 2 * n

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

/-- **The power of 2 in an even primitive non-deficient number is below its radical.** Let $n$
be an even primitive non-deficient number, that is, a positive integer with $\sigma(n) \ge 2n$
all of whose proper divisors $m$ satisfy $\sigma(m) < 2m$, where $\sigma$ is the sum of divisors.
If $2^a$ is the largest power of $2$ dividing $n$ and $R$ is the product of the distinct primes
dividing $n$, then $2^{a+1} < R$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Proposition
(label `evenprimitivenondeficientshaveatightbound`). -/
theorem_wanted two_pow_factorization_add_one_lt_radical
    (n : ℕ) (hne : Even n)
    (hn : IsPrimitiveNondeficient n) :
    2 ^ (n.factorization 2 + 1) < ∏ q ∈ n.primeFactors, q

/-- **Zelinsky's reciprocal bound.** For real numbers $k$ and $m$ with $k \ge 2$ and
$0 < m < 1/(k(k+1))$, we have $1/(1 - km) < 1 + (k+1)m$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `KMlemma`). -/
theorem_wanted one_div_one_sub_mul_lt_add
    (k m : ℝ) (hk : 2 ≤ k) (hm0 : 0 < m)
    (hm : m < 1 / (k * (k + 1))) :
    1 / (1 - k * m) < 1 + (k + 1) * m

/-- **Abundancy ratio at an exactly dividing prime power.** Let $n$ be a positive integer, $p$ a
prime and $a \ge 1$ an integer such that $p^a$ exactly divides $n$ (that is, $p^a \mid n$ and
$p^{a+1} \nmid n$). Then $h(n)/h(n/p) \le 1 + 1/p^a$, where $h(m) = \sigma(m)/m$ is the abundancy
index and $\sigma(m)$ is the sum of the positive divisors of $m$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `correctedPAlemma`). -/
theorem_wanted abundancyIndex_div_le
    (n p a : ℕ) (hn0 : 0 < n) (hp : p.Prime) (ha : 1 ≤ a)
    (hpa : n.factorization p = a) :
    abundancyIndex n / abundancyIndex (n / p) ≤
      1 + 1 / (p : ℚ) ^ a

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
