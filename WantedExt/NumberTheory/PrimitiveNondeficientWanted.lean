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

/-- Zelinsky's *non-deficient*: a positive integer with
`σ(n) ≥ 2n`. (Positivity is part of the notion: with
`Nat.divisors 0 = ∅` the bare divisor-sum inequality would make
`0` vacuously non-deficient.) -/
def IsNondeficient (n : ℕ) : Prop :=
  n ≠ 0 ∧ 2 * n ≤ ∑ d ∈ Nat.divisors n, d

/-- Zelinsky's *primitive non-deficient*: non-deficient, with every
proper divisor deficient. -/
def IsPrimitiveNondeficient (n : ℕ) : Prop :=
  IsNondeficient n ∧
    ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m

/-- The paper's abundancy `h(n) = σ(n)/n`, in `ℚ`. The paper
defines `h` for positive `n`; at `n = 0` this returns `0` by
`ℚ`-division totalization, and every use below assumes `0 < n`. -/
noncomputable def abundancyIndex (n : ℕ) : ℚ :=
  ((∑ d ∈ Nat.divisors n, d : ℕ) : ℚ) / (n : ℚ)

/-- The paper's `H(n) = ∏_{p ∣ n} p/(p-1)`, in `ℚ`. The paper
defines `H` for positive `n`; at `n = 0` the empty product makes
this `1`, and every use below assumes `n ≠ 0`. -/
noncomputable def abundancySup (n : ℕ) : ℚ :=
  ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)

/-- **Lemma** (classification for `k = 2`, even case): for an odd
prime `p`, `2^a * p` is primitive non-deficient iff
`2^a < p ≤ 2^(a+1) - 1`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), first
part. -/
theorem_wanted isPrimitiveNondeficient_two_pow_mul_prime_iff
    (a p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) :
    IsPrimitiveNondeficient (2 ^ a * p) ↔
      2 ^ a < p ∧ p ≤ 2 ^ (a + 1) - 1

/-- **Lemma** (classification for `k = 2`, odd case): all odd
numbers with exactly two distinct prime divisors are deficient.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), second
part. -/
theorem_wanted deficient_of_odd_card_primeFactors_eq_two
    (n : ℕ) (hno : Odd n) (hk : n.primeFactors.card = 2) :
    ∑ d ∈ Nat.divisors n, d < 2 * n

/-- **Lemma**: an odd primitive non-deficient number with `k = 3`
or `k = 4` distinct prime factors has a prime factor `p` with
`p^(a+1) < 2R`, where `a` is the exponent of `p` and `R` the
radical.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Checkforexactly3or4distinctprimefactors`). -/
theorem_wanted exists_pow_factorization_add_one_lt_two_mul_radical
    (n : ℕ) (hno : Odd n) (hn : IsPrimitiveNondeficient n)
    (hk : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * ∏ q ∈ n.primeFactors, q

/-- **Lemma** (Grün): if `n` is non-deficient with least prime
factor `p₁` and `k` distinct prime factors, then
`(3/2) p₁ - 2 < k`, and if `p₁ ≥ 5` then `p₁ + 2 ≤ k`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `Grun`). -/
theorem_wanted grun_bounds_of_isNondeficient
    (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) :
    (3 : ℚ) / 2 * (p₁ : ℚ) - 2 < (n.primeFactors.card : ℚ) ∧
      (5 ≤ p₁ → p₁ + 2 ≤ n.primeFactors.card)

/-- **Proposition**: if `n` is an even primitive non-deficient
number and `2^a` exactly divides `n`, then `2^(a+1) < R`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Proposition
(label `evenprimitivenondeficientshaveatightbound`). -/
theorem_wanted two_pow_factorization_add_one_lt_radical
    (n : ℕ) (hne : Even n)
    (hn : IsPrimitiveNondeficient n) :
    2 ^ (n.factorization 2 + 1) < ∏ q ∈ n.primeFactors, q

/-- **Lemma**: for real `k ≥ 2` and `0 < m < 1/(k(k+1))`,
`1/(1 - km) < 1 + (k+1)m`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `KMlemma`). -/
theorem_wanted one_div_one_sub_mul_lt_add
    (k m : ℝ) (hk : 2 ≤ k) (hm0 : 0 < m)
    (hm : m < 1 / (k * (k + 1))) :
    1 / (1 - k * m) < 1 + (k + 1) * m

/-- **Lemma**: if `p^a` exactly divides the positive integer `n`,
then `h(n)/h(n/p) ≤ 1 + 1/p^a`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `correctedPAlemma`). -/
theorem_wanted abundancyIndex_div_le
    (n p a : ℕ) (hn0 : 0 < n) (hp : p.Prime) (ha : 1 ≤ a)
    (hpa : n.factorization p = a) :
    abundancyIndex n / abundancyIndex (n / p) ≤
      1 + 1 / (p : ℚ) ^ a

/-- **Lemma** (generalized Puchta): let `n` be primitive
non-deficient with least prime factor `p₁` and `k` distinct prime
factors, `(p₁, k) ≠ (3, 3)`, and suppose `H(n) ≥ 2 + α` for some
`0 < α < 1`. Then some prime factor `p` satisfies
`p^(a+1) < max (2(k+2+p₁)/α) (k(k+1))`, where `a` is the exponent
of `p`.

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

/-- **Proposition** (dichotomy): if `n` is an odd primitive
non-deficient number with least prime factor `p₁`, greatest prime
factor `p_k`, `k` distinct prime factors, and radical `R`, then
either `p_k < √R` or some prime factor `p` satisfies
`p^(a+1) < (k + 2 + p₁)(p_k - 1)`, where `a` is the exponent
of `p`.

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
