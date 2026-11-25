/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackSequences

/-!
# Tests for throwback sequences

With all weights equal to one, the first two original indices trade places at each step.
-/

open MetaMathlibExt

/-- Every index past the first two stays in its original position. -/
example (k p : ℕ) (hp : 1 < p) : ((throwback (fun _ : ℕ => 1))^[k] id) p = p := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Function.iterate_succ_apply', throwback, hp.not_gt, hp.ne'] using ih

/-- The original leader leads again at every even time. -/
example : {k | ((throwback (fun _ : ℕ => 1))^[k] id) 0 = 0}.Infinite := by
  have even_time (k : ℕ) : ((throwback (fun _ : ℕ => 1))^[2 * k] id) 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simpa [Nat.mul_succ, Function.iterate_succ_apply', throwback] using ih
  exact Set.infinite_of_forall_exists_gt fun n => ⟨2 * (n + 1), even_time (n + 1), by omega⟩

/-- Once the initial partial placement fills a position, all later stages preserve it. -/
example (k : ℕ) : partialPlacement (fun i => i + 1) k (-2) = some 1 := by
  induction k with
  | zero => decide
  | succ k ih => simp [partialPlacement, ih]
