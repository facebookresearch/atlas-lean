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

namespace MetaMathlibExt

@[expose] public section

/-- The integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with each coefficient
`λⱼ ∈ {-1, m}`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7. -/
public def IsSignedPowTwoSum (m s t : ℕ) (n : ℤ) : Prop :=
  ∃ lam : ℕ → ℤ, (∀ j ∈ Finset.Icc s t, lam j = -1 ∨ lam j = (m : ℤ)) ∧
    n = ∑ j ∈ Finset.Icc s t, lam j * 2 ^ j

/-- Characteristic example: with `m = 3`, `s = 0`, `t = 1`, the value
`3 * 1 + (-1) * 2 = 1` is a signed power-of-two sum.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7. -/
public theorem isSignedPowTwoSum_one : IsSignedPowTwoSum 3 0 1 1 := by
  refine ⟨fun j => if j = 0 then 3 else -1, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
  · have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
    rw [hIcc]
    simp

/-- Interval and congruence characterization of signed power-of-two sums.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and
`m ≥ 1`, the integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with
`λⱼ ∈ {-1, m}` are precisely the integers `n` in the interval
`[-2^s * (2^{t-s+1} - 1), 2^s * m * (2^{t-s+1} - 1)]` satisfying
`n ≡ -2^s * (2^{t-s+1} - 1) [ZMOD 2^s * (m + 1)]`.

Verified by brute-force enumeration for `m ∈ {1, 2, 3, 5}`, `s ≤ 2`,
`t - s ≤ 3` before formalizing. -/
public theorem_wanted isSignedPowTwoSum_iff (m s t : ℕ) (hm : 1 ≤ m)
    (hst : s ≤ t) (n : ℤ) :
    IsSignedPowTwoSum m s t n ↔
      -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) ≤ n ∧
      n ≤ 2 ^ s * (m : ℤ) * (2 ^ (t - s + 1) - 1) ∧
      n ≡ -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) [ZMOD 2 ^ s * ((m : ℤ) + 1)]

/-- Extension of signed power-of-two sums to longer intervals.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let
`β = ν₂(m + 1)`. If `n` is a signed power-of-two sum over `[s, t]` with
`t ≥ s + β - 1`, then `n` is also expressible over `[s, t + α]` whenever
`2^α ≡ 1 [(m + 1) / 2^β]`.

The hypothesis `t ≥ s + β - 1` is written as `s + β ≤ t + 1` to cover the
case `β = 0`. -/
public theorem_wanted isSignedPowTwoSum_extend (m s t α : ℕ) (hm : 1 ≤ m)
    (hβ : s + (m + 1).factorization 2 ≤ t + 1)
    (hα : 2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)])
    (n : ℤ) (h : IsSignedPowTwoSum m s t n) :
    IsSignedPowTwoSum m s (t + α) n

/-- Characterization of `1 + ∑ λⱼ * 2^j` with `λⱼ ∈ {-1, 1}`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 12 (`jis-2024-24.7.5-lem-12`): an integer `n` can be
written as `1 + ∑_{j=1}^{k} λⱼ * 2^j` for some `k ≥ 1` and coefficients
`λⱼ ∈ {-1, 1}` if and only if `n ≡ 3 [ZMOD 4]`. -/
public theorem_wanted one_add_signedPowTwoSum_iff (n : ℤ) :
    (∃ k : ℕ, 1 ≤ k ∧ ∃ lam : ℕ → ℤ,
      (∀ j ∈ Finset.Icc 1 k, lam j = -1 ∨ lam j = 1) ∧
      n = 1 + ∑ j ∈ Finset.Icc 1 k, lam j * 2 ^ j) ↔ n ≡ 3 [ZMOD 4]

/-- An integer `n` with `|n| > 1` is `S`-perfect (of the first kind) if
`n = 1 + ∑ λ_d * d`, the sum over the positive divisors `d` of `n` with
`1 < d < |n|`, with every weight `λ_d ∈ S`. The set `𝒫(S)` of the paper is
`{n | IsSPerfect S n}`.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Section 1 (definition of `S`-perfect numbers of the first
kind). -/
public def IsSPerfect (S : Set ℤ) (n : ℤ) : Prop :=
  1 < n.natAbs ∧ ∃ lam : ℕ → ℤ, (∀ d ∈ n.natAbs.properDivisors.erase 1, lam d ∈ S) ∧
    n = 1 + ∑ d ∈ n.natAbs.properDivisors.erase 1, lam d * d

/-- Characteristic example: `6 = 1 + 2 + 3` is `{1}`-perfect (an ordinary
perfect number).

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Example 2 (`S = {1}`). -/
public theorem isSPerfect_one_six : IsSPerfect {1} 6 := by
  refine ⟨by decide, fun _ => 1, fun _ _ => rfl, ?_⟩
  decide

/-- Characteristic example: `12 = 1 - 2 + 3 + 4 + 6` is `{-1, 1}`-perfect.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Example 2 (`S = {-1, 1}`). -/
public theorem isSPerfect_neg_one_one_twelve : IsSPerfect {-1, 1} 12 := by
  refine ⟨by decide, fun d => if d = 2 then -1 else 1, ?_, ?_⟩
  · intro d _
    by_cases h : d = 2 <;> simp [h]
  · decide

/-- Characteristic non-example: a prime `p` is not `S`-perfect for any `S`,
since the defining sum is empty.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Proposition 3 (the prime-power case with exponent one). -/
public theorem not_isSPerfect_prime (S : Set ℤ) {p : ℕ} (hp : p.Prime) :
    ¬ IsSPerfect S p := by
  rintro ⟨-, lam, -, h⟩
  have : (p : ℤ).natAbs.properDivisors.erase 1 = ∅ := by
    rw [Int.natAbs_natCast, Nat.Prime.properDivisors hp]
    simp
  rw [this, Finset.sum_empty] at h
  have := hp.two_le
  omega

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
