/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log

/-!
# Halving sequences of natural numbers

A sequence `a : ℕ → ℕ` halves at step `i` when `2 * a (i + 1) ≤ a i`. After `k` halving
steps, `2 ^ k * a k ≤ a 0`, so an index `k` at which the value is still positive satisfies
`k ≤ Nat.log 2 (a 0)`. This bounds the number of completed halvings, that is, the index of
the last positive term, not the number of positive terms: for `a 0 = 1` the only positive
term is `a 0`, at index `0 = Nat.log 2 1`.

## Main results

* `MathlibExt.Nat.two_pow_mul_le_of_halving`: after `k` halving steps, `2 ^ k * a k ≤ a 0`.
* `MathlibExt.Nat.le_log_of_halving_of_pos`: if `a k` is positive after `k` halving steps,
  then `k ≤ Nat.log 2 (a 0)`.
* `MathlibExt.Nat.le_div_two_pow_of_halving`: if `a 0 ≤ n` and `a (k + 1) ≤ a k / 2` for
  every `k`, then `a k ≤ n / 2 ^ k`.
* `MathlibExt.Nat.le_log_of_halving`: under the same hypotheses, every index `k` with
  `0 < a k` satisfies `k ≤ Nat.log 2 n`.

The Hopcroft counting lemmas `DFA.Hopcroft.mul_pow_le_card_of_halving_chain` and
`DFA.Hopcroft.smaller_half_chain_le_log` in `CSLibExt` apply the first two results to block
cardinalities.
-/

@[expose] public section

namespace MathlibExt.Nat

/-- After `k` halving steps, the initial value is at least `2 ^ k` times the value at `k`.
Only the steps before `k` are used. -/
theorem two_pow_mul_le_of_halving {a : ℕ → ℕ} {k : ℕ}
    (hstep : ∀ i, i < k → 2 * a (i + 1) ≤ a i) : 2 ^ k * a k ≤ a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc 2 ^ (k + 1) * a (k + 1) = 2 ^ k * (2 * a (k + 1)) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ k * a k := Nat.mul_le_mul_left _ (hstep k (Nat.lt_succ_self k))
      _ ≤ a 0 := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)

/-- If the value is still positive after `k` halving steps, then `k ≤ Nat.log 2 (a 0)`:
at most `Nat.log 2 (a 0)` halvings complete while the value stays positive. -/
theorem le_log_of_halving_of_pos {a : ℕ → ℕ} {k : ℕ}
    (hstep : ∀ i, i < k → 2 * a (i + 1) ≤ a i) (hk : 0 < a k) :
    k ≤ Nat.log 2 (a 0) := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ k * a k := Nat.mul_le_mul_left _ hk
    _ ≤ a 0 := two_pow_mul_le_of_halving hstep

/-- If `a 0 ≤ n` and every step at least halves the value (`a (k + 1) ≤ a k / 2`), then
after `k` steps `a k ≤ n / 2 ^ k`. -/
theorem le_div_two_pow_of_halving (a : ℕ → ℕ) (n : ℕ)
    (h0 : a 0 ≤ n) (hstep : ∀ k, a (k + 1) ≤ a k / 2) (k : ℕ) :
    a k ≤ n / 2 ^ k := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      calc a (k + 1) ≤ a k / 2 := hstep k
        _ ≤ (n / 2 ^ k) / 2 := Nat.div_le_div_right ih
        _ = n / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- Under the hypotheses of `le_div_two_pow_of_halving`, every index `k` with `0 < a k`
satisfies `k ≤ Nat.log 2 n`. This bounds the index of the last positive term, that is, the
number of completed halvings, not the number of positive terms. -/
theorem le_log_of_halving (a : ℕ → ℕ) (n : ℕ)
    (h0 : a 0 ≤ n) (hstep : ∀ k, a (k + 1) ≤ a k / 2) (k : ℕ)
    (hk : 0 < a k) : k ≤ Nat.log 2 n := by
  have hbound := le_div_two_pow_of_halving a n h0 hstep k
  have hpos : 1 ≤ n / 2 ^ k := lt_of_lt_of_le hk hbound
  have h2k : (2 : ℕ) ^ k ≤ n :=
    (Nat.one_le_div_iff (Nat.pow_pos Nat.two_pos)).mp hpos
  exact Nat.le_log_of_pow_le Nat.one_lt_two h2k

end MathlibExt.Nat
