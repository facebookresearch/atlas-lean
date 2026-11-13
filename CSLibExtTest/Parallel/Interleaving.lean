/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Parallel.Interleaving

@[expose] public section

/-- Boundary check: running a trace of writes ends at the last
write. -/
example : runTrace 0 [(0, RegOp.write 3), (1, RegOp.read),
    (0, RegOp.write 5)] = 5 := rfl

/-- Boundary check: projecting an interleaving onto thread 0
recovers thread 0's operations. -/
example : project 0 [(0, RegOp.write 3), (1, RegOp.read),
    (0, RegOp.read)] = [RegOp.write 3, RegOp.read] := rfl

/-- Thread 0 writes `1`, then reads. -/
def thread₀ : List (ℕ × RegOp) := [(0, RegOp.write 1), (0, RegOp.read)]

/-- Thread 1 writes `2`, then `3`. -/
def thread₁ : List (ℕ × RegOp) := [(1, RegOp.write 2), (1, RegOp.write 3)]

/-- An interleaving that alternates between the two threads. -/
def interleaved : List (ℕ × RegOp) :=
  [(0, RegOp.write 1), (1, RegOp.write 2), (0, RegOp.read), (1, RegOp.write 3)]

/-- `interleaved` is a shuffle of `thread₀` and `thread₁`. -/
theorem interleaved_shuffle : Shuffle thread₀ thread₁ interleaved :=
  .left _ (.right _ (.left _ (.right _ .nil)))

/-- `project_shuffle_left` on the concrete shuffle: thread 0's
operations come back in their original order. -/
example : project 0 interleaved = [RegOp.write 1, RegOp.read] :=
  project_shuffle_left (by decide) (by decide) interleaved_shuffle

/-- `project_shuffle_right` on the concrete shuffle: thread 1's
operations come back in their original order. -/
example : project 1 interleaved = [RegOp.write 2, RegOp.write 3] :=
  project_shuffle_right (by decide) (by decide) interleaved_shuffle
