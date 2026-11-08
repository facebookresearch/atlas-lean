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

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7. -/
public def IsSignedPowTwoSum (m s t : ℕ) (n : ℤ) : Prop :=
  ∃ lam : ℕ → ℤ, (∀ j ∈ Finset.Icc s t, lam j = -1 ∨ lam j = (m : ℤ)) ∧
    n = ∑ j ∈ Finset.Icc s t, lam j * 2 ^ j

/-- Characteristic example: with `m = 3`, `s = 0`, `t = 1`, the value
`3 * 1 + (-1) * 2 = 1` is a signed power-of-two sum.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7. -/
public theorem isSignedPowTwoSum_one : IsSignedPowTwoSum 3 0 1 1 := by
  refine ⟨fun j => if j = 0 then 3 else -1, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
  · have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
    rw [hIcc]
    simp

/-- Interval and congruence characterization of signed power-of-two sums.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and
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

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let
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

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 12 (`jis-2024-24.7.5-lem-12`): an integer `n` can be
written as `1 + ∑_{j=1}^{k} λⱼ * 2^j` for some `k ≥ 1` and coefficients
`λⱼ ∈ {-1, 1}` if and only if `n ≡ 3 [ZMOD 4]`. -/
public theorem_wanted one_add_signedPowTwoSum_iff (n : ℤ) :
    (∃ k : ℕ, 1 ≤ k ∧ ∃ lam : ℕ → ℤ,
      (∀ j ∈ Finset.Icc 1 k, lam j = -1 ∨ lam j = 1) ∧
      n = 1 + ∑ j ∈ Finset.Icc 1 k, lam j * 2 ^ j) ↔ n ≡ 3 [ZMOD 4]

end

end MetaMathlibExt
