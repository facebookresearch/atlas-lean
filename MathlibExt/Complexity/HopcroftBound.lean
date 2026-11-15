/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-!
# Smaller-half processing bound

Hopcroft's DFA minimization processes the smaller half of a split
block; this module proves the counting core of its total-work
bound: a block size that at least halves at every round is at
most `n / 2 ^ k` after `k` rounds, so a positive block survives
at most `Nat.log 2 n` rounds. The minimization construction
itself is not formalized here.
-/

@[expose] public section

/-- Smaller-half processing bound (counting core of Hopcroft
minimization, MOD-20): if a block size at least halves at every
processing round, then after `k` rounds it is at most
`n / 2 ^ k`, and a positive block can only be processed
`Nat.log 2 n` times. -/
theorem smaller_half_bound (a : ℕ → ℕ) (n : ℕ)
    (h0 : a 0 ≤ n) (hstep : ∀ k, a (k + 1) ≤ a k / 2) (k : ℕ) :
    a k ≤ n / 2 ^ k := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      calc a (k + 1) ≤ a k / 2 := hstep k
        _ ≤ (n / 2 ^ k) / 2 := Nat.div_le_div_right ih
        _ = n / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

theorem smaller_half_rounds (a : ℕ → ℕ) (n : ℕ) (hn : 0 < n)
    (h0 : a 0 ≤ n) (hstep : ∀ k, a (k + 1) ≤ a k / 2) (k : ℕ)
    (hk : 0 < a k) : k ≤ Nat.log 2 n := by
  have hbound := smaller_half_bound a n h0 hstep k
  have hpos : 1 ≤ n / 2 ^ k := lt_of_lt_of_le hk hbound
  have h2k : (2 : ℕ) ^ k ≤ n :=
    (Nat.one_le_div_iff (pow_pos (by norm_num) k)).mp hpos
  exact Nat.le_log_of_pow_le (by norm_num) h2k

end
