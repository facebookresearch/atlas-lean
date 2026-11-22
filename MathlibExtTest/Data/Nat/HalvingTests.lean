/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Nat.Halving

@[expose] public section

open MathlibExt.Nat

/-- Exact halving `8, 4, 2, 1` satisfies the step hypothesis up to `k = 3`. -/
example : 2 ^ 3 * (fun i : ℕ => 2 ^ (3 - i)) 3 ≤ (fun i : ℕ => 2 ^ (3 - i)) 0 :=
  two_pow_mul_le_of_halving (a := fun i : ℕ => 2 ^ (3 - i)) (k := 3) (by decide)

/-- Only the steps before `k` are used: `8, 4, 2, 1, 100` is still positive at index `3`,
which is `Nat.log 2 8`, even though it grows afterwards. -/
example : 3 ≤ Nat.log 2 ((fun i : ℕ => if i ≤ 3 then 2 ^ (3 - i) else 100) 0) :=
  le_log_of_halving_of_pos (a := fun i : ℕ => if i ≤ 3 then 2 ^ (3 - i) else 100) (k := 3)
    (by decide) (by decide)

/-- After 4 halvings from at most 16, at most 1 remains. -/
example (a : ℕ → ℕ) (h0 : a 0 ≤ 16) (hstep : ∀ k, a (k + 1) ≤ a k / 2) :
    a 4 ≤ 1 :=
  le_div_two_pow_of_halving a 16 h0 hstep 4

/-- `a k = 16 / 2 ^ k` halves at every step and is positive at index `4`. -/
example : 4 ≤ Nat.log 2 16 :=
  le_log_of_halving (fun k => 16 / 2 ^ k) 16 (by simp)
    (fun k => by simp [Nat.div_div_eq_div_mul, Nat.pow_succ]) 4 (by decide)

/-- With the previous example, `Nat.log 2 16 = 4` shows that `le_log_of_halving` is
attained. -/
example : Nat.log 2 16 = 4 :=
  Nat.log_pow Nat.one_lt_two 4

/-- Tight boundary `n = 1`: a positive value can occur only at index `0`, so the bound counts
completed halvings rather than positive terms. -/
example (a : ℕ → ℕ) (h0 : a 0 ≤ 1) (hstep : ∀ k, a (k + 1) ≤ a k / 2) (k : ℕ)
    (hk : 0 < a k) : k = 0 := by
  have h := le_log_of_halving a 1 h0 hstep k hk
  rw [Nat.log_one_right] at h
  exact Nat.le_zero.mp h

end
