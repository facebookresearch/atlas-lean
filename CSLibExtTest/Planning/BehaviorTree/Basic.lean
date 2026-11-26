/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.BehaviorTree.Basic

/-! # Tests of current-state switching and sampled execution -/

open Cslib.Planning.BehaviorTree

namespace CSLibExtTest.BehaviorTree

variable (δ : TimeStep)

private def gate : Tree ℕ δ where
  next n := n + 1
  status n := if n = 0 then .running else .success

private def back : Tree ℕ δ where
  next n := n - 1
  status n := if n = 1 then .failure else .running

-- At 0 the gate is still running. At 1 it hands off: reading the second child
-- at 2 instead of 1 would give both the wrong update and the wrong return.
example : ((gate δ).sequence (back δ)).status 0 = .running ∧
    ((gate δ).sequence (back δ)).next 0 = 1 ∧
    ((gate δ).sequence (back δ)).status 1 = .failure ∧
    ((gate δ).sequence (back δ)).next 1 = 0 := ⟨rfl, rfl, rfl, rfl⟩

-- Reactivity: after the second child returns the state to 0, the first is selected again.
example : ((gate δ).sequence (back δ)).stateAt 0 3 = 1 := rfl

-- The first child's failure, not its running return, triggers fallback.
example : ((back δ).fallback (gate δ)).next 1 = 2 ∧
    ((back δ).fallback (gate δ)).status 1 = .success ∧
    ((back δ).fallback (gate δ)).next 0 = 0 ∧
    ((back δ).fallback (gate δ)).status 0 = .running := ⟨rfl, rfl, rfl, rfl⟩

-- A third child with completely arbitrary maps is skipped in either bracketing.
example (c : Tree ℕ δ) : (((gate δ).sequence (back δ)).sequence c).next 1 = 0 ∧
    ((gate δ).sequence ((back δ).sequence c)).status 1 = .failure := ⟨rfl, rfl⟩

-- The original real-vector state space, without regularity assumptions on its return map.
example {n : ℕ} (r : (Fin n → ℝ) → Status) (x : Fin n → ℝ) (i : Fin n) :
    let T : RealTree n δ := ⟨fun v j => -v j, r⟩
    T.stateAt x 2 i = x i ∧ T.status x = r x := by
  exact ⟨neg_neg _, rfl⟩

end CSLibExtTest.BehaviorTree
