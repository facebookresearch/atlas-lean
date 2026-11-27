/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackLeaderTime

/-!
# Recursive leader-time bound for the positive integers

At position two the recursive bound is three steps, and the initial row attains it.
-/

namespace MetaMathlibExt.throwback_leader_time_le

private def positiveIntegers (i : ℕ) : ℕ := i + 1

private theorem row_pos (m i : ℕ) : 0 < ((throwback id)^[m] positiveIntegers) i := by
  induction m generalizing i with
  | zero => exact Nat.succ_pos _
  | succ m ih =>
    simp only [Function.iterate_succ_apply', throwback, id_eq]
    split_ifs <;> exact ih _

example (m : ℕ) : ∃ k ≤ 3,
    throwbackSequence positiveIntegers (m + k) = ((throwback id)^[m] positiveIntegers) 2 := by
  have hprev (t : ℕ) : ∃ k ≤ 1,
      throwbackSequence positiveIntegers (t + k) = ((throwback id)^[t] positiveIntegers) 1 :=
    ⟨1, le_rfl, by simp [throwbackSequence, Function.iterate_succ_apply', throwback, row_pos]⟩
  have hcount : Set.ncard {i | positiveIntegers i < 2} = 1 := by
    have : {i | positiveIntegers i < 2} = ({0} : Set ℕ) := by
      ext i
      change positiveIntegers i < 2 ↔ i = 0
      unfold positiveIntegers
      omega
    rw [this, Set.ncard_singleton]
  have hinj : Function.Injective positiveIntegers := by
    intro i j hij
    exact Nat.succ.inj hij
  exact throwback_leader_time_le positiveIntegers Nat.succ_pos hinj 2 (by decide) 1 1
    hprev (by simpa only [hcount] using hprev) m

example : ([0, 1, 2, 3] : List ℕ).map (throwbackSequence positiveIntegers) = [1, 2, 1, 3] := by
  decide

end MetaMathlibExt.throwback_leader_time_le
