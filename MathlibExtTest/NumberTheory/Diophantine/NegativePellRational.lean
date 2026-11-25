/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Diophantine.NegativePellRational
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for `MathlibExt.NumberTheory.Diophantine.NegativePellRational` -/

namespace MathlibExtTest.NegativePellRational

open MetaMathlibExt

-- `d = 3`: the prime `3 ≡ 3 (mod 4)` divides `d`, so `x² - 3 y² = -1` has no rational solution.
example : ¬∃ x y : ℚ, x ^ 2 - 3 * y ^ 2 = -1 := by
  intro h
  have h' : ∃ x y : ℚ, x ^ 2 - ((3 : ℕ) : ℚ) * y ^ 2 = -1 := by exact_mod_cast h
  exact (negPell_rat_solvable_iff 3 (by norm_num) Nat.prime_three.squarefree).mp h' 3
    Nat.prime_three dvd_rfl (by norm_num)

-- `d = 6 = 2 · 3`: one prime divisor `≡ 3 (mod 4)` is enough to rule out rational solutions.
example : ¬∃ x y : ℚ, x ^ 2 - ((6 : ℕ) : ℚ) * y ^ 2 = -1 := fun h =>
  have hsq : Squarefree (2 * 3) :=
    (Nat.squarefree_mul (by decide)).mpr ⟨Nat.squarefree_two, Nat.prime_three.squarefree⟩
  (negPell_rat_solvable_iff 6 (by norm_num) hsq).mp h 3 Nat.prime_three (by norm_num)
    (by norm_num)

-- `d = 34 = 2 · 17`: no prime divisor is `≡ 3 (mod 4)`, so there is a rational solution, such as
-- `(3 / 5, 1 / 5)` from `34 = 3² + 5²`.
example : ∃ x y : ℚ, x ^ 2 - ((34 : ℕ) : ℚ) * y ^ 2 = -1 := by
  have h17 : Nat.Prime 17 := by norm_num
  have hsq : Squarefree (2 * 17) :=
    (Nat.squarefree_mul (by decide)).mpr ⟨Nat.squarefree_two, h17.squarefree⟩
  refine (negPell_rat_solvable_iff 34 (by norm_num) hsq).mpr fun p hp hpd => ?_
  rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 17 from hpd) with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp h17).mp h]
    norm_num

example : (3 / 5 : ℚ) ^ 2 - ((34 : ℕ) : ℚ) * (1 / 5) ^ 2 = -1 := by norm_num

-- `d = 1`, outside the source's range `d > 1`: `1` has no prime divisor, and `(0, 1)` is a
-- solution of `x² - y² = -1`.
example : ∃ x y : ℚ, x ^ 2 - ((1 : ℕ) : ℚ) * y ^ 2 = -1 :=
  (negPell_rat_solvable_iff 1 one_pos squarefree_one).mpr fun _ hp hpd =>
    absurd (Nat.dvd_one.mp hpd) hp.ne_one

-- The hypothesis `Squarefree d` cannot be dropped: for `d = 9`, `(0, 1 / 3)` is a rational
-- solution, but the prime divisor `3` of `9` is `≡ 3 (mod 4)`.
example : (∃ x y : ℚ, x ^ 2 - ((9 : ℕ) : ℚ) * y ^ 2 = -1) ∧
    ¬∀ p : ℕ, p.Prime → p ∣ 9 → p % 4 ≠ 3 :=
  ⟨⟨0, 1 / 3, by norm_num⟩, fun h => h 3 Nat.prime_three (by norm_num) (by norm_num)⟩

end MathlibExtTest.NegativePellRational
