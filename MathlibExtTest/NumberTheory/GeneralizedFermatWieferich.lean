/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatWieferich

/-! # Tests for squared prime factors of generalized Fermat numbers -/

open MetaMathlibExt

-- The bases 7 and 2 have the same residue modulo 5. Only 7 satisfies the congruence modulo 25.
example : 5 ^ 2 ∣ 7 ^ 2 ^ 1 + 1 := by
  apply (sq_dvd_pow_two_pow_add_one_iff_wieferich (by decide) (by decide) (by decide)).mpr
  exact ⟨by decide, orderOf_eq_prime_pow (by decide) (by decide)⟩

example : ¬ 5 ^ 2 ∣ 2 ^ 2 ^ 1 + 1 := by
  intro h
  have hw := ((sq_dvd_pow_two_pow_add_one_iff_wieferich (by decide) (by decide) (by decide)).mp h).1
  exact (by decide : ¬ 2 ^ (5 - 1) ≡ 1 [MOD 5 ^ 2]) hw

-- At n = 0, the criterion detects a base congruent to -1 modulo the prime square.
example : orderOf (8 : ZMod 3) = 2 := by
  have h := (sq_dvd_pow_two_pow_add_one_iff_wieferich (a := 8) (p := 3) (n := 0)
    (by decide) (by decide) (by decide)).mp (by decide)
  simpa using h.2

-- The order condition excludes base one at every index.
example (n : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 1 ^ 2 ^ n + 1 := by
  rw [sq_dvd_pow_two_pow_add_one_iff_wieferich hp hp2 (by simpa using hp.ne_one)]
  simp [(Nat.one_lt_pow n.succ_ne_zero (by decide : 1 < 2)).ne]
