/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.BooleanFunctions.Certificate

/-!
# Tests for decision-tree certificates

* `majTree`, the majority of three bits, queries `0` and `1` and then `2` only when they disagree.
  Its depth is `3`. On `110` (both first answers `true`) and `001` (both `false`) the path queries
  `{0, 1}`, and changing the unqueried bit `2` does not change the value; on `101` it queries all
  three variables, which attains the depth bound.
* `repeatTree` queries `0` twice on the same path. Its depth is `2`, but only one variable is
  queried, so the depth bound is strict.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.Certificate

open StatMech StatMech.OSSS

/-- The majority of three bits: query `0` and `1`, and query `2` only when they disagree. -/
def majTree : DecisionTree (Fin 3) :=
  .node 0 (.node 1 (.leaf true) (.node 2 (.leaf true) (.leaf false)))
    (.node 1 (.node 2 (.leaf true) (.leaf false)) (.leaf false))

example : majTree.depth = 3 := rfl

/-! ### The path where both first answers are `true` -/

example : majTree.eval ![true, true, false] = true := by decide

example : majTree.queried ![true, true, false] = {0, 1} := by decide

example : (majTree.queried ![true, true, false]).card ≤ majTree.depth :=
  majTree.card_queried_le_depth _

/-- Flipping the unqueried bit `2` keeps the value. -/
example : majTree.eval ![true, true, true] = majTree.eval ![true, true, false] :=
  majTree.eval_eq_of_agree_on_queried _ _ (by decide)

/-! ### The path where both first answers are `false` -/

example : majTree.eval ![false, false, true] = false := by decide

example : majTree.queried ![false, false, true] = {0, 1} := by decide

example : majTree.eval ![false, false, false] = majTree.eval ![false, false, true] :=
  majTree.eval_eq_of_agree_on_queried _ _ (by decide)

/-! ### A path that queries every variable -/

example : majTree.eval ![true, false, true] = true := by decide

example : majTree.queried ![true, false, true] = {0, 1, 2} := by decide

/-- On `101` the queried set has as many variables as the depth. -/
example : (majTree.queried ![true, false, true]).card = majTree.depth := by decide

/-- Bit `2` is queried on `101`, and flipping it changes the value. -/
example : majTree.eval ![true, false, false] ≠ majTree.eval ![true, false, true] := by decide

/-! ### A repeated query -/

/-- A tree that queries `0` twice on the path of an input with `0` set. -/
def repeatTree : DecisionTree (Fin 2) :=
  .node 0 (.node 0 (.leaf true) (.leaf false)) (.leaf false)

example : repeatTree.depth = 2 := rfl

example : repeatTree.eval ![true, false] = true := by decide

example : repeatTree.queried ![true, false] = {0} := by decide

example : (repeatTree.queried ![true, false]).card < repeatTree.depth := by decide

example : repeatTree.eval ![true, true] = repeatTree.eval ![true, false] :=
  repeatTree.eval_eq_of_agree_on_queried _ _ (by decide)

end StatMechTest.BooleanFunctions.Certificate
