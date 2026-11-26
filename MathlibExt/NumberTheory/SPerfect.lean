/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors

/-!
# Weighted perfect numbers

Ross allows a weight from a fixed set of integers on each proper divisor greater than one.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
