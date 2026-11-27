/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.KeyTheorems.NaturalProofs

open MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs

-- The low input bit changes first. Even a function on zero bits has one truth-table entry.
example : truthTable (n := 2) (fun x => x 0) = [false, true, false, true] := by decide
example : truthTable (n := 2) (fun x => x 1) = [false, false, true, true] := by decide
example : truthTable (n := 0) (fun _ => true) = [true] := by decide

-- Repeating a true predecessor preserves AND. A forward reference reads false for both gates.
example : npCircuitEval [(0, [0]), (3, [0, 0]), (3, [0, 9]), (4, [9, 1])] [true] =
    [true, true, false, true] := by decide

-- Empty fan-in has a different identity for each connective.
example : npCircuitEval [(3, []), (4, [])] [] = [true, false] := by decide

-- A fixed one-gate circuit witnesses the size bound at every length, including zero.
example : PRFInPPoly (fun _ _ _ => true) := by
  refine ⟨1, fun n => ⟨[(1, [1])], by simp, fun key input => ?_⟩⟩
  rfl
