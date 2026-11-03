/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Revealment
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for the revealment of a decision tree

Tests for `CSLibExt.Complexity.BooleanFunctions.Revealment` on the two-variable `AND` tree
`andTree` at `p = 1/2` (weight `νHalf`):

* `depth` at small trees (`decide`);
* `reveal` of `andTree`: `1` at the root coordinate and `1/2` at the second coordinate;
* `sum_reveal_eq_expect_card`: both sides equal `3/2`;
* `sum_reveal_le_depth`: the instance `3/2 ≤ 2`;
* `reveal_le_one`, and `reveal_le_of_queried_imp` with the predicate `ω true`, which is
  tight for `andTree` (both sides are `1/2`); `reveal_le_of_queried_imp_or` at the same
  coordinate.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.Revealment

example : depth andTree = 2 := by decide
example : depth dictTree = 1 := by decide
example : depth (DecisionTree.leaf (E := Bool) true) = 0 := rfl

/-- The summed revealment of `andTree` at `p = 1/2` is `3/2`. -/
lemma sum_reveal_andTree : ∑ e, reveal νHalf andTree e = 3 / 2 := by
  rw [Fintype.sum_bool, reveal_andTree_true, reveal_andTree_false]; norm_num

/-- `sum_reveal_eq_expect_card`: `andTree` makes `3/2` queries on average. -/
example : expect νHalf (fun ω => ((andTree.queried ω).card : ℝ)) = 3 / 2 := by
  rw [← sum_reveal_eq_expect_card, sum_reveal_andTree]

/-- The expected query count of `andTree`, computed directly. -/
example : expect νHalf (fun ω => ((andTree.queried ω).card : ℝ)) = 3 / 2 := by
  simp [expect, weight, sum_configSpace_bool, andTree, DecisionTree.queried, bernoulliWeight]
  norm_num

/-- `sum_reveal_le_depth` for `andTree`: `3/2 ≤ 2`. -/
example : (3 / 2 : ℝ) ≤ 2 := by
  have h := sum_reveal_le_depth νHalf_isProbWeight andTree
  rw [sum_reveal_andTree, show depth andTree = 2 by decide] at h
  exact_mod_cast h

example (e : Bool) : reveal νHalf andTree e ≤ 1 := reveal_le_one νHalf_isProbWeight _ e

/-- `false` is queried by `andTree` only when `ω true` holds. -/
lemma andTree_queried_false_imp (ω : ConfigSpace Bool) (h : false ∈ andTree.queried ω) :
    ω true = true := by
  revert h; cases hω : ω true <;> simp [andTree, DecisionTree.queried, hω]

/-- `reveal_le_of_queried_imp` bounds the revealment of `false` by `P(ω true) = 1/2`; the
bound is attained (`reveal_andTree_false`). -/
example : reveal νHalf andTree false ≤ 1 / 2 := by
  have h := reveal_le_of_queried_imp νHalf_isProbWeight andTree false (fun ω => ω true = true)
    andTree_queried_false_imp
  have hP : expect νHalf (fun ω => if ω true = true then (1 : ℝ) else 0) = 1 / 2 := by
    simp [expect, weight, sum_configSpace_bool, bernoulliWeight]; norm_num
  rwa [hP] at h

example : reveal νHalf andTree false
    ≤ expect νHalf (fun ω => if ω true = true then (1 : ℝ) else 0)
      + expect νHalf (fun ω => if ω false = true then (1 : ℝ) else 0) :=
  reveal_le_of_queried_imp_or νHalf_isProbWeight andTree false _ _
    fun ω h => Or.inl (andTree_queried_false_imp ω h)

end StatMechTest.BooleanFunctions
