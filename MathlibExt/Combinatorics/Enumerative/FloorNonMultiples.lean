/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Operations

/-!
# Floor enumeration of non-multiples

`MetaMathlibExt.image_floor_eq_nonMultiples` enumerates the positive non-multiples of
a natural number by a floor function.
-/

namespace MetaMathlibExt

/-- **The non-multiples of an integer as values of a floor function.** For every integer $u \ge 2$,
the set $\{\lfloor (un - 1)/(u - 1) \rfloor : n \ge 1\}$, with $n$ ranging over the positive
integers, is the set of positive integers not divisible by $u$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Lemma 2 (`integers-2026-A53-lem-2`). -/
public theorem image_floor_eq_nonMultiples {u : ℕ} (hu : 2 ≤ u) :
    (fun n => (u * n - 1) / (u - 1)) '' {n | 1 ≤ n} = {m | 1 ≤ m ∧ ¬ u ∣ m} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  have hd : 0 < d := by omega
  -- The r-th index in block q gives the r-th nonzero residue in that block.
  have block (q r : ℕ) (hr : 0 < r) (hrd : r ≤ d) :
      ((d + 1) * (d * q + r) - 1) / d = (d + 1) * q + r := by
    have h : (d + 1) * (d * q + r) - 1 = d * ((d + 1) * q + r) + (r - 1) := by
      simp only [Nat.succ_mul, Nat.mul_add]
      omega
    rw [h, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  ext m
  constructor
  · rintro ⟨n, hn, rfl⟩
    change 1 ≤ n at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hr := Nat.mod_lt k hd
    have hk : k + 1 = d * (k / d) + (k % d + 1) := by
      have := Nat.mod_add_div k d
      omega
    simp only [Set.mem_ofPred_eq, Nat.succ_sub_one, Nat.succ_eq_add_one]
    rw [hk, block _ _ (by omega) (by omega), Nat.dvd_iff_mod_eq_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : k % d + 1 < d + 1)]
    omega
  · rintro ⟨_, hdiv⟩
    have hr : 0 < m % (d + 1) := Nat.pos_of_ne_zero (fun h => hdiv (Nat.dvd_of_mod_eq_zero h))
    have hrd : m % (d + 1) < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
    refine ⟨d * (m / (d + 1)) + m % (d + 1), ?_, ?_⟩
    · change 1 ≤ d * (m / (d + 1)) + m % (d + 1)
      omega
    · exact (block _ _ hr (by omega)).trans (Nat.div_add_mod m (d + 1))

end MetaMathlibExt
