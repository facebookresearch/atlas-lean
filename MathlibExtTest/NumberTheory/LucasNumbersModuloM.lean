/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasNumbersModuloM
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.LucasNumbersModuloM` -/

namespace MathlibExtTest.NumberTheory.LucasNumbersModuloM

open MathlibExt.NumberTheory.LucasNumbersModuloMWanted MetaMathlibExt

-- The first Lucas numbers: `2, 1, 3, 4, 7, 11, 18`.
example : lucasNumber 6 = 18 := rfl

/-- A modulus outside the classification misses some residue. -/
private theorem exists_missed {m : ℕ} (hm : 1 < m)
    (hlist : ¬(m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 7 ∨ m = 14 ∨ ∃ k : ℕ, 1 ≤ k ∧ m = 3 ^ k)) :
    ∃ r < m, ∀ n, lucasNumber n % m ≠ r := by
  by_contra h
  refine hlist ((Statement_holds m hm).1 fun r hr => ?_)
  by_contra h'
  exact h ⟨r, hr, fun n hn => h' ⟨n, hn⟩⟩

/-- A modulus with a prime factor other than `3` is not a power of `3`. -/
private theorem not_three_pow {m q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) (hqm : q ∣ m) :
    ¬∃ k : ℕ, 1 ≤ k ∧ m = 3 ^ k := by
  rintro ⟨k, -, rfl⟩
  exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow hqm))

-- Every residue modulo `3 ^ 20` is a Lucas number: far beyond a direct computation.
example : ∀ r < 3 ^ 20, ∃ n, lucasNumber n % 3 ^ 20 = r :=
  (Statement_holds (3 ^ 20) (by norm_num)).2 <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨20, by norm_num, rfl⟩

-- The largest exceptional modulus, `14`.
example : ∀ r < 14, ∃ n, lucasNumber n % 14 = r :=
  (Statement_holds 14 (by norm_num)).2 (by norm_num)

-- Modulo the prime `5` some residue is missed (it is `0`: `L_n mod 5` cycles `2, 1, 3, 4`).
example : ∃ r < 5, ∀ n, lucasNumber n % 5 ≠ r :=
  exists_missed (by norm_num) fun h => by
    rcases h with h | h | h | h | h | h
    any_goals norm_num at h
    exact not_three_pow Nat.prime_five (by norm_num) dvd_rfl h

-- Every residue modulo `3` and modulo `4` is attained, but not modulo `12`.
example : ∃ r < 12, ∀ n, lucasNumber n % 12 ≠ r :=
  exists_missed (by norm_num) fun h => by
    rcases h with h | h | h | h | h | h
    any_goals norm_num at h
    exact not_three_pow Nat.prime_two (by norm_num) (by norm_num) h

-- The same for `10 = 2 · 5`, although every residue modulo `2` is attained.
example : ∃ r < 10, ∀ n, lucasNumber n % 10 ≠ r :=
  exists_missed (by norm_num) fun h => by
    rcases h with h | h | h | h | h | h
    any_goals norm_num at h
    exact not_three_pow Nat.prime_two (by norm_num) (by norm_num) h

-- The hypothesis `1 < m` matters: modulo `1` every residue is attained, yet `1` is not listed.
example : (∀ r < 1, ∃ n, lucasNumber n % 1 = r) ∧
    ¬(1 = 2 ∨ 1 = 4 ∨ 1 = 6 ∨ 1 = 7 ∨ 1 = 14 ∨ ∃ k : ℕ, 1 ≤ k ∧ 1 = 3 ^ k) := by
  refine ⟨fun r hr => ⟨0, by omega⟩, ?_⟩
  rintro (h | h | h | h | h | ⟨k, hk, h⟩)
  any_goals norm_num at h
  have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

end MathlibExtTest.NumberTheory.LucasNumbersModuloM
