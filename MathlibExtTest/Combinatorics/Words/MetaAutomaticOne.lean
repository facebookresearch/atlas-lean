/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticOne

open MetaMathlibExt

-- The initial pair and the first nested pair have opposite orientations.
example : [0, 1, 2, 3].map metaAutomaticOne = [false, true, true, false] := by
  decide +kernel

-- In these blocks the nested index selects the even and odd positions, respectively.
example : [26, 27, 30, 31].map metaAutomaticOne = [false, true, true, false] := by
  decide +kernel

-- Either value at an even index determines the following value.
example (n : ℕ) : metaAutomaticOne (2 * n + 1) = !metaAutomaticOne (2 * n) := by
  have h := metaAutomaticOne_balanced n
  cases he : metaAutomaticOne (2 * n) <;> cases ho : metaAutomaticOne (2 * n + 1) <;>
    simp_all

/-- The nested companion `b(m) = ℳ₁(2m + 1 - ℳ₁(m))` of the sequence `ℳ₁`. -/
private def companion (m : ℕ) : Bool :=
  metaAutomaticOne (2 * m + 1 - (metaAutomaticOne m).toNat)

-- Direct evaluation agrees with the four identities for `n ≤ 16`, including `n = 0`, which the
-- source's hypothesis `n ≥ 1` leaves out.
example : ∀ n ∈ List.range 17,
    (metaAutomaticOne (4 * n), companion (4 * n)) = (metaAutomaticOne n, companion n) ∧
      (metaAutomaticOne (4 * n + 1), companion (4 * n + 1)) =
        (!metaAutomaticOne n, xor (metaAutomaticOne n) (companion n)) ∧
      (metaAutomaticOne (4 * n + 2), companion (4 * n + 2)) =
        (companion n, !metaAutomaticOne n) ∧
      (metaAutomaticOne (4 * n + 3), companion (4 * n + 3)) =
        (!companion n, !xor (metaAutomaticOne n) (companion n)) := by
  decide +kernel

-- The second coordinate at `4n + 2` is the complement of `ℳ₁(n)`.
example (n : ℕ) (hn : 1 ≤ n) : companion (4 * n + 2) = !metaAutomaticOne n :=
  congrArg Prod.snd (metaAutomaticOne_pair_closure companion (fun _ => rfl) n hn).2.2.1

-- Iterating the first identity: the pair is constant along `n, 4n, 16n, ...` when `n ≥ 1`.
example (k n : ℕ) (hn : 1 ≤ n) :
    (metaAutomaticOne (4 ^ k * n), companion (4 ^ k * n)) =
      (metaAutomaticOne n, companion n) := by
  induction k with
  | zero => rw [Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    have hk : 1 ≤ 4 ^ k * n := Nat.mul_pos (Nat.pow_pos (by decide)) hn
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ k) 4, Nat.mul_assoc]
    exact (metaAutomaticOne_pair_closure companion (fun _ => rfl) _ hk).1.trans ih
