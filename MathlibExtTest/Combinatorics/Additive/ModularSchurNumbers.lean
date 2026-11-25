/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.ModEq
import MathlibExt.Combinatorics.Additive.ModularSchurNumbers

/-! # Tests for modular Schur numbers -/

open MetaMathlibExt

-- Five copies of 2 sum to 0 modulo 5, so the singleton is sum-free at this arity.
example : IsSumFreeMod 5 5 {2} := by
  by_contra h
  have criterion := (not_isSumFreeMod_singleton_iff 2 5 5 (by decide) (by decide) (by decide)).1
  exact (by decide : ¬ 5 ≡ 1 [MOD 5]) ((criterion (by decide)).mp h)

-- Four copies of 4 give 4 modulo 6. The arity is 1 modulo 3, although it is 4 modulo 6.
example : ¬ IsSumFreeMod 6 4 {4} := by
  have criterion := (not_isSumFreeMod_singleton_iff 4 4 6 (by decide) (by decide) (by decide)).2
  exact (criterion (by decide)).mpr (by decide)

-- At the arity threshold for 3², elements with distinct residues modulo 3 cannot form a class.
example : ¬ IsSumFreeMod 9 8 {8, 4} := by
  intro h
  exact (by decide : ¬ 8 ≡ 4 [MOD 3])
    (modEq_of_isSumFreeMod_pair 3 8 4 2 8 (by decide) (by decide) (by decide) (by decide) h)

-- A sum-free pair at the same threshold can have distinct residues modulo 9.
example : IsSumFreeMod 9 8 {1, 4} := by
  intro x hx y hy hsum
  have hres {z : ℤ} (hz : z ∈ ({1, 4} : Set ℤ)) : z ≡ 1 [ZMOD 3] := by
    rcases Set.mem_insert_iff.mp hz with rfl | rfl <;> decide
  have hxsum : ∑ j, x j ≡ 8 [ZMOD 3] := by
    simpa using Int.ModEq.sum (s := Finset.univ) (fun j _ => hres (hx j))
  exact (by decide : ¬ (8 : ℤ) ≡ 1 [ZMOD 3])
    (hxsum.symm.trans ((hsum.of_dvd (by decide : (3 : ℤ) ∣ 9)).trans (hres hy)))

-- At the color threshold, the range includes a nonunit residue (2 modulo 4).
example : modularSchurNumber 4 3 2 = 3 :=
  modularSchurNumber_prime_pow_eq 2 2 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- Extra colors may be empty.
example : modularSchurNumber 9 10 3 = 8 :=
  modularSchurNumber_prime_pow_eq 3 2 10 3 (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- When the arity is 1 modulo the prime, three copies of 2 already obstruct a partition.
example : ¬ HasSumFreePartitionMod 4 3 3 2 := by
  rintro ⟨c, hc⟩
  apply hc (c 2) (fun _ => 2) _ 2 _ (by decide)
  · exact fun _ => ⟨2, by decide, le_rfl, rfl, rfl⟩
  · exact ⟨2, by decide, le_rfl, rfl, rfl⟩

-- At the smallest allowed modulus and color count, 7 is in the exceptional class.
example : modularSchurNumber 4 2 7 = 1 :=
  (modularSchurNumber_two_mul 2 7 2 (by decide) (by decide) (by decide) (by decide)).1 (by decide)

-- Arity equal to the modulus allows 1 and 2 to receive distinct colors.
example : 2 ≤ modularSchurNumber 4 2 4 :=
  (modularSchurNumber_two_mul 2 4 2 (by decide) (by decide) (by decide) (by decide)).2 (by decide)

-- At the color threshold, the modulus can have two distinct prime factors.
example : modularSchurNumber 6 5 8 = 5 := by
  apply modularSchurNumber_eq_sub_one 6 5 8 (by decide) (by decide) _ (by decide)
  intro d hd hd1 h
  have hcommon : d ∣ Nat.gcd 6 (8 - 1) := Nat.dvd_gcd hd h.symm.dvd'
  exact hd1 (Nat.dvd_one.mp hcommon)
