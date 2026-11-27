/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.SPerfect
public import MathlibExt.NumberTheory.SignedBinarySum

namespace MetaMathlibExt

@[expose] public section

/-- Integers with at least two distinct prime factors are `S`-perfect for some
finite `S` with `#S ≤ τ(n) - 2`; prime powers are never `S`-perfect.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Proposition 3 (`jis-2024-24.7.5-prop-3`). "At least two prime
factors" is read as at least two distinct prime factors, as the second claim
(prime powers) requires. -/
public theorem_wanted exists_finset_isSPerfect_and_not_isSPerfect_of_isPrimePow :
    (∀ n : ℤ, 1 < n.natAbs.primeFactors.card →
      ∃ S : Finset ℤ, S.card ≤ n.natAbs.divisors.card - 2 ∧ IsSPerfect (S : Set ℤ) n) ∧
    (∀ n : ℤ, IsPrimePow n.natAbs → ∀ S : Set ℤ, ¬ IsSPerfect S n)

/-- Monotonicity of `𝒫(S)` under unions and intersections of weight sets.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Proposition 4 (`jis-2024-24.7.5-prop-4`). -/
public theorem_wanted iUnion_setOf_isSPerfect_subset_and_setOf_isSPerfect_iInter_subset
    {ι : Type*} (S : ι → Set ℤ) :
    (⋃ i, {n : ℤ | IsSPerfect (S i) n}) ⊆ {n : ℤ | IsSPerfect (⋃ i, S i) n} ∧
    {n : ℤ | IsSPerfect (⋂ i, S i) n} ⊆ ⋂ i, {n : ℤ | IsSPerfect (S i) n}

/-- If `n` is `{0, m}`-perfect with `m ≥ 1`, then so is `(m + 1) * n`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 5 (`jis-2024-24.7.5-lem-5`). No sign hypothesis is
needed: a `{0, m}`-perfect number satisfies `n - 1 ≥ 0`. -/
public theorem_wanted isSPerfect_zero_mul_succ (m : ℕ) (hm : 1 ≤ m) (n : ℤ)
    (h : IsSPerfect {0, (m : ℤ)} n) : IsSPerfect {0, (m : ℤ)} ((m + 1) * n)

/-- There are infinitely many (positive) `{0, m}`-perfect numbers for every
`m ≥ 1`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Theorem 6 (`jis-2024-24.7.5-thm-6`). -/
public theorem_wanted setOf_isSPerfect_zero_infinite (m : ℕ) (hm : 1 ≤ m) :
    {n : ℕ | IsSPerfect {0, (m : ℤ)} n}.Infinite

/-- Characterization of `{-1, m}`-perfect numbers of the form `2^k p` along
powers of two: with `β = ν₂(m + 1)`, if `2^k p` and `2^(k+α) p` are both
`{-1, m}`-perfect (`p` an odd prime, `k, α ≥ 1`) then
`2^α ≡ 1 [(m + 1) / 2^β]`; conversely, if `2^k p` is `{-1, m}`-perfect with
`k ≥ β` then so is `2^(k+α) p` whenever `2^α ≡ 1 [(m + 1) / 2^β]`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Theorem 9 (`jis-2024-24.7.5-thm-9`). The converse is stated
for every `α : ℕ` (the case `α = 0` is trivial). -/
public theorem_wanted isSPerfect_neg_one_two_pow_mul_prime_iff (m : ℕ) (hm : 1 ≤ m)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ k α : ℕ, 1 ≤ k → 1 ≤ α →
      IsSPerfect {-1, (m : ℤ)} (2 ^ k * p) → IsSPerfect {-1, (m : ℤ)} (2 ^ (k + α) * p) →
      2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)]) ∧
    (∀ k α : ℕ, (m + 1).factorization 2 ≤ k →
      IsSPerfect {-1, (m : ℤ)} (2 ^ k * p) →
      2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)] →
      IsSPerfect {-1, (m : ℤ)} (2 ^ (k + α) * p))

/-- Construction of `{-1, m}`-perfect numbers `2^k p`: with `β = ν₂(m + 1)`
and `α > β` such that `2^α ≡ 1 [(m + 1) / 2^β]`, every prime
`p ≡ 2 (2^(α+1) - 1) - 1 [2 (m + 1)]` has `2^k p` `{-1, m}`-perfect for some
`k ≥ α`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Theorem 10 (`jis-2024-24.7.5-thm-10`). -/
public theorem_wanted exists_isSPerfect_neg_one_two_pow_mul_prime (m α p : ℕ) (hm : 1 ≤ m)
    (hαβ : (m + 1).factorization 2 < α)
    (hα : 2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)])
    (hp : p.Prime) (hpmod : (p : ℤ) ≡ 2 * (2 ^ (α + 1) - 1) - 1 [ZMOD 2 * ((m : ℤ) + 1)]) :
    ∃ k, α ≤ k ∧ IsSPerfect {-1, (m : ℤ)} (2 ^ k * p)

/-- There are infinitely many (positive) `{-1, m}`-perfect numbers for every
`m ≥ 1`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Corollary 11 (`jis-2024-24.7.5-cor-11`). -/
public theorem_wanted setOf_isSPerfect_neg_one_infinite (m : ℕ) (hm : 1 ≤ m) :
    {n : ℕ | IsSPerfect {-1, (m : ℤ)} n}.Infinite

/-- Prime-power lifting for `{-1, 1}`-perfect numbers: for a prime `p ∤ n`,
(a) if `n` is `{-1, 1}`-perfect then so is `n p^k` for every `k ≥ 1`;
(b) if `n p` is `{-1, 1}`-perfect then so is `n p^(2k-1)` for every `k ≥ 1`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 13 (`jis-2024-24.7.5-lem-13`). -/
public theorem_wanted isSPerfect_neg_one_one_mul_prime_pow (n : ℤ) (p : ℕ) (hp : p.Prime)
    (hpn : ¬ (p : ℤ) ∣ n) :
    (IsSPerfect {-1, 1} n → ∀ k, 1 ≤ k → IsSPerfect {-1, 1} (n * p ^ k)) ∧
    (IsSPerfect {-1, 1} (n * p) → ∀ k, 1 ≤ k → IsSPerfect {-1, 1} (n * p ^ (2 * k - 1)))

/-- If `n` is `{-1, 1}`-perfect, then so is `2 n`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 14 (`jis-2024-24.7.5-lem-14`). Stated for all integers
`n`; the paper's proof does not use the sign of `n`. -/
public theorem_wanted isSPerfect_neg_one_one_two_mul (n : ℤ) (h : IsSPerfect {-1, 1} n) :
    IsSPerfect {-1, 1} (2 * n)

/-- Even `{-1, 1}`-perfect numbers: if `d ≥ 1` is odd and not a square, then
`2^k d` is `{-1, 1}`-perfect for all sufficiently large `k`; conversely, if
`2^k d` is `{-1, 1}`-perfect for some `k ≥ 0` and `d ≥ 1`, then `d` is not a
square.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Theorem 15 (`jis-2024-24.7.5-thm-15`). "All but finitely many
`k ≥ 1`" is written as "for all `k ≥ K`" for some `K`. -/
public theorem_wanted isSPerfect_neg_one_one_two_pow_mul_iff :
    (∀ d : ℕ, Odd d → ¬ IsSquare d →
      ∃ K, ∀ k ≥ K, IsSPerfect {-1, 1} (2 ^ k * d)) ∧
    (∀ k d : ℕ, 1 ≤ d → IsSPerfect {-1, 1} (2 ^ k * d) → ¬ IsSquare d)

end

end MetaMathlibExt
