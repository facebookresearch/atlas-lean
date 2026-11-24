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
# Enumerating positive nonmultiples by a floor formula
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
  have hd : 0 < u - 1 := by omega
  -- A block of u - 1 positive indices maps to the corresponding nonmultiples of u.
  have hfloor (q r : ℕ) (hr : 0 < r) (hru : r < u) :
      (u * ((u - 1) * q + r) - 1) / (u - 1) = u * q + r := by
    have hsucc : u - 1 + 1 = u := by omega
    have hmul : u * r = (u - 1) * r + r := by
      simpa only [Nat.add_mul, Nat.one_mul] using congrArg (· * r) hsucc.symm
    have hnum : u * ((u - 1) * q + r) - 1 = (u - 1) * (u * q + r) + (r - 1) := by
      rw [Nat.mul_add u, Nat.mul_left_comm u (u - 1), hmul,
        Nat.mul_add (u - 1), Nat.add_assoc]
      omega
    rw [hnum, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega : r - 1 < u - 1), Nat.add_zero]
  ext m
  constructor
  · rintro ⟨n, hn, rfl⟩
    change 1 ≤ n at hn
    -- Divide n - 1 so the shifted remainder is always positive.
    let q := (n - 1) / (u - 1)
    let r := (n - 1) % (u - 1) + 1
    have hr : 0 < r := Nat.succ_pos _
    have hru : r < u := by
      dsimp [r]
      have := Nat.mod_lt (n - 1) hd
      omega
    have hn' : (u - 1) * q + r = n := by
      dsimp [q, r]
      have := Nat.mod_add_div (n - 1) (u - 1)
      omega
    change 1 ≤ (u * n - 1) / (u - 1) ∧ ¬ u ∣ (u * n - 1) / (u - 1)
    rw [← hn', hfloor q r hr hru]
    refine ⟨by omega, ?_⟩
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hru]
    exact Nat.ne_of_gt hr
  · rintro ⟨_, hm⟩
    have hu' : 0 < u := by omega
    have hr : 0 < m % u := by
      exact Nat.pos_of_ne_zero (fun h => hm (Nat.dvd_of_mod_eq_zero h))
    refine ⟨(u - 1) * (m / u) + m % u, ?_, ?_⟩
    · change 1 ≤ (u - 1) * (m / u) + m % u
      omega
    · dsimp only
      rw [hfloor _ _ hr (Nat.mod_lt m hu'), Nat.add_comm, Nat.mod_add_div]

end MetaMathlibExt
