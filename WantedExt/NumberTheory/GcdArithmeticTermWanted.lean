/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- The sequence `s_{a,b}(n)` with generating function `f_{a,b}(z) = 1 / ((z^a - 1)(z^b - 1))`,
taken as the coefficients of the inverse power series over `ℚ` (the constant coefficient of
`(X^a - 1)(X^b - 1)` is `1` for `a, b ≥ 1`).

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Section 2 (definition of `s_{a,b}`). -/
public noncomputable def gcdTermSeq (a b n : ℕ) : ℚ :=
  coeff n (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹

/-- `s_{a,b}(0) = 1` for `a, b ≥ 1`.

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem gcdTermSeq_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : gcdTermSeq a b 0 = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  simp [gcdTermSeq, ha', hb']

/-- The generating function identity `(z^a - 1)(z^b - 1) · ∑ s_{a,b}(n) zⁿ = 1` for
`a, b ≥ 1`.

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem mul_mk_gcdTermSeq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1) * PowerSeries.mk (gcdTermSeq a b) = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  have hmk : PowerSeries.mk (gcdTermSeq a b) =
      (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹ := by
    ext n
    simp [gcdTermSeq]
  rw [hmk]
  apply PowerSeries.mul_inv_cancel
  simp [ha', hb']

/-- The sequence `s_{a,b}` takes natural-number values, and `s_{a,b}(ab) = gcd(a, b) + 1`.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 4. -/
public theorem_wanted gcdTermSeq_natural_and_eq_gcd_add_one (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (∀ n, ∃ m : ℕ, gcdTermSeq a b n = m) ∧ gcdTermSeq a b (a * b) = Nat.gcd a b + 1

/-- If `a, b ≥ 1` and one of them exceeds `1`, then `s_{a,b}(n) ≤ s_{1,1}(n) = n + 1` for every
`n`, with equality only for `n = 0`.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 5. -/
public theorem_wanted gcdTermSeq_le_gcdTermSeq_one_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 1 < a ∨ 1 < b) (n : ℕ) :
    gcdTermSeq a b n ≤ gcdTermSeq 1 1 n ∧ gcdTermSeq 1 1 n = n + 1 ∧
      (gcdTermSeq a b n = gcdTermSeq 1 1 n → n = 0)

/-- For all `a, b ≥ 1`,
`gcd(a, b) = (⌊5^{ab(ab+a+b)} / ((5^{a²b} - 1)(5^{ab²} - 1))⌋ mod 5^{ab}) - 1`, stated without
truncated subtraction as `gcd(a, b) + 1 = ⋯` in `ℕ`.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Theorem 1. -/
public theorem_wanted gcd_add_one_eq_floor_div_mod_five (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.gcd a b + 1 =
      5 ^ (a * b * (a * b + a + b)) / ((5 ^ (a ^ 2 * b) - 1) * (5 ^ (a * b ^ 2) - 1)) %
        5 ^ (a * b)

/-- For all `a, b ≥ 1`,
`gcd(a, b) = (((-5^{ab(ab+a+b)}) mod ((5^{a²b} - 1)(5^{ab²} - 1))) mod 5^{ab}) - 2` over `ℤ`,
with the nonnegative remainder.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 1. -/
public theorem_wanted gcd_eq_neg_emod_emod_five_sub_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Nat.gcd a b : ℤ) =
      (-(5 : ℤ) ^ (a * b * (a * b + a + b))) %
            (((5 : ℤ) ^ (a ^ 2 * b) - 1) * ((5 : ℤ) ^ (a * b ^ 2) - 1)) % (5 : ℤ) ^ (a * b) - 2

/-- For the bases `c ∈ {2, 3, 4}` and all `a, b ≥ 1`, both identities
`gcd(a, b) = (⌊c^{ab(ab+a+b)} / ((c^{a²b} - 1)(c^{ab²} - 1))⌋ mod c^{ab}) - 1` and
`gcd(a, b) = (((-c^{ab(ab+a+b)}) mod ((c^{a²b} - 1)(c^{ab²} - 1))) mod c^{ab}) - 2` hold exactly
when `(a, b) ≠ (1, 1)` (for `(1, 1)` both fail: "the unique exception"). Both identities are
stated over `ℤ` with `Int.ediv`/`Int.emod` (floor and nonnegative remainder for positive
divisors). The record's closing remark on which cases remain to verify is proof commentary
and is not formalized.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2. -/
public theorem_wanted gcd_arithmetic_terms_small_bases (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1 ↔ (a, b) ≠ (1, 1)) ∧
      ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2 ↔ (a, b) ≠ (1, 1))

end

end MetaMathlibExt
