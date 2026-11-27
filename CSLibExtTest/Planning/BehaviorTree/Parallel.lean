/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.BehaviorTree.Parallel

/-! # Tests of disjoint writes with cross-coordinate reads -/

open Cslib.Planning.BehaviorTree

namespace CSLibExtTest.BehaviorTree

variable (δ : TimeStep)

private def left : LeftChild Bool Bool δ :=
  leftChild Prod.snd fun p => if p.2 then .success else .running

private def right : RightChild Bool Bool δ :=
  rightChild Prod.fst fun p => if p.1 then .running else .failure

-- A simultaneous cross-coordinate swap, not either order of sequential overwrites.
example (m : Threshold) (p : Bool × Bool) : (parallel m (left δ) (right δ)).next p = p.swap := rfl

-- Both statuses see the pre-swap input: success/failure at (false, true), but
-- running/running at (true, false). The threshold affects the return, not the swap.
example : (parallel .one (left δ) (right δ)).status (false, true) = .success ∧
    (parallel .two (left δ) (right δ)).status (false, true) = .failure ∧
    (parallel .one (left δ) (right δ)).status (true, false) = .running ∧
    (parallel .two (left δ) (right δ)).status (true, false) = .running := ⟨rfl, rfl, rfl, rfl⟩

example : Threshold.one.combine .running .failure = .running ∧
    Threshold.two.combine .running .failure = .failure ∧
    Threshold.one.combine .running .success = .success ∧
    Threshold.two.combine .running .success = .running := by decide

end CSLibExtTest.BehaviorTree
