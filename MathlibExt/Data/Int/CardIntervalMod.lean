/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.CardIntervalMod

/-!
# Counting residue classes with integer representatives

Normalize the integer representative before counting natural numbers in its residue class.

## References

* The normalization argument comes from `sum_residueIndicator_range` in
  `MathlibExt.NumberTheory.DigitSumCongruenceCount`.
-/

/-- **Counting natural numbers in an integer residue class.**

For `q > 0`, the number of naturals less than `n` congruent to the integer `r` modulo
`q` is `n / q` (natural division), plus one if the least nonnegative residue of `r` is less
than `n % q`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Lemma 4. -/
public theorem Nat.count_intModEq_card {q : ℕ} (hq : 0 < q) (r : ℤ) (n : ℕ) :
    Nat.count (fun i : ℕ => (i : ℤ) ≡ r [ZMOD q]) n =
      n / q + if r % q < ((n % q : ℕ) : ℤ) then 1 else 0 := by
  let u := (r % q).toNat
  have hu : (u : ℤ) = r % q := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq.ne'))
  have hmod (i : ℕ) : (i : ℤ) ≡ r [ZMOD q] ↔ i ≡ u [MOD q] := by
    rw [← Int.natCast_modEq_iff, hu]
    exact ⟨fun h => h.trans (Int.mod_modEq r q).symm, fun h => h.trans (Int.mod_modEq r q)⟩
  have hlt : (u % q < n % q) ↔ r % q < ((n % q : ℕ) : ℤ) := by
    rw [← Int.ofNat_lt, Int.natCast_emod, hu, Int.emod_emod]
  simp only [hmod, Nat.count_modEq_card n hq, hlt]
