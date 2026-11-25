/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MathlibExt.NumberTheory.FkPerfectWanted

-- At exponent zero the equation holds with `l = 0`, but not with positive `l`.
example : KLNearPerfectWith 3 0 (2 * 3 ^ 0) 1 := by
  unfold KLNearPerfectWith
  decide

example (l d : ℕ) (hl : 1 ≤ l) : ¬ KLNearPerfectWith 3 l (2 * 3 ^ 0) d := by
  rintro ⟨hd, hlt, hsum⟩
  have hs : (∑ e ∈ (2 * 3 ^ 0 : ℕ).divisors, e ^ 3) = 9 := by decide
  rw [hs] at hsum
  change d ∣ 2 at hd
  change d < 2 at hlt
  change 9 = 8 + d ^ 3 + l * 2 at hsum
  have hd1 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (Nat.ne_of_lt hlt)
  rw [hd1, one_pow] at hsum
  omega

-- At exponent one the square divisibility holds for `p = 3, k = 3`, but no divisor works.
example (l d : ℕ) : ¬ KLNearPerfectWith 3 l (2 * 3 ^ 1) d := by
  rintro ⟨hd, hlt, hsum⟩
  have hs : (∑ e ∈ (2 * 3 ^ 1 : ℕ).divisors, e ^ 3) = 252 := by decide
  rw [hs] at hsum
  change d ∣ 6 at hd
  change d < 6 at hlt
  change 252 = 216 + d ^ 3 + l * 6 at hsum
  interval_cases d <;> norm_num at hd <;> norm_num at hsum <;> omega

-- Two witnesses from Table 2: an even exponent with an odd divisor, and vice versa.
example : (3 : ℕ) ^ 2 ∣ 1 + 2 ^ 3 ∧ (Even (2 : ℕ) ↔ Odd (3 : ℕ)) :=
  klNearPerfectWith_two_mul_prime_pow_imp 3 2 3 53 3 (by decide) (by decide) (by decide)
    (by decide) (by unfold KLNearPerfectWith; decide)

example : (3 : ℕ) ^ 2 ∣ 1 + 2 ^ 9 ∧ (Even (3 : ℕ) ↔ Odd (6 : ℕ)) :=
  klNearPerfectWith_two_mul_prime_pow_imp 3 3 9 144895263260 6 (by decide) (by decide)
    (by decide) (by decide) (by unfold KLNearPerfectWith; decide)

-- The conclusion excludes `p = 3` when `k = 2`, for every exponent.
example (a l d : ℕ) (hl : 1 ≤ l) : ¬ KLNearPerfectWith 2 l (2 * 3 ^ a) d := by
  intro h
  exact (by decide : ¬ (3 : ℕ) ^ 2 ∣ 1 + 2 ^ 2)
    (klNearPerfectWith_two_mul_prime_pow_imp 3 a 2 l d (by decide) (by decide) (by decide) hl h).1

end MathlibExt.NumberTheory.FkPerfectWanted
