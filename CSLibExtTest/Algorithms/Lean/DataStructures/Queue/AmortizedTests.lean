/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Queue.Amortized

import all Init.Data.Queue

@[expose] public section

/-!
# Tests for the amortized cost of `Std.Queue`

These examples exercise enqueueing, empty dequeue, buffered dequeue, the rear-list reversal path,
and a mixed operation sequence.
-/

namespace Cslib.Algorithms.Lean.Queue.AmortizedTests

open Amortized

private def empty : Std.Queue Nat :=
  Std.Queue.empty

private def buffered : Std.Queue Nat :=
  { eList := [3, 2], dList := [1] }

private def rearOnly : Std.Queue Nat :=
  { eList := [3, 2, 1], dList := [] }

example : potential empty = 0 := by rfl

example : (enqueue empty 1).ret = { eList := [1], dList := [] } := by rfl
example : (enqueue empty 1).time = 1 := by rfl

example : (dequeue empty).ret = (none, empty) := by rfl
example : (dequeue empty).time = 1 := by rfl

example : (dequeue buffered).ret = (some 1, { eList := [3, 2], dList := [] }) := by rfl
example : (dequeue buffered).time = 1 := by rfl

example : (dequeue rearOnly).ret = (some 1, { eList := [], dList := [2, 3] }) := by rfl
example : (dequeue rearOnly).time = 4 := by rfl

example (q : Std.Queue Nat) (value : Nat) :
    (enqueue q value).time + potential (enqueue q value).ret = potential q + 2 :=
  enqueue_amortized q value

example (q : Std.Queue Nat) :
    (dequeue q).time + potential (dequeue q).ret.2 = potential q + 1 :=
  dequeue_amortized q

private def operations : List (Operation Nat) :=
  [.enqueue 1, .enqueue 2, .enqueue 3, .dequeue, .dequeue, .dequeue, .dequeue]

example : totalCharge operations = 10 := by rfl
example : (run operations empty).time = 10 := by rfl
example : potential (run operations empty).ret = 0 := by rfl

example (ops : List (Operation Nat)) (q : Std.Queue Nat) :
    (run ops q).time + potential (run ops q).ret = potential q + totalCharge ops :=
  run_amortized ops q

example (ops : List (Operation Nat)) (q : Std.Queue Nat) :
    (run ops q).time ≤ potential q + 2 * ops.length :=
  run_time_le_potential_add_twice_length ops q

end Cslib.Algorithms.Lean.Queue.AmortizedTests
