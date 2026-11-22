/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BeliefPropagation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Tests for belief propagation

* The two-vertex tree Bayesian network `rain → wet` (prior `P(rain) = 1/5` at the root,
  `P(wet | rain) = 9/10`, `P(wet | no rain) = 1/10` on the edge): belief propagation gives the
  marginal of the leaf, `P(wet) = 13/50`, which the root-only variable elimination does not
  compute.
* The path `0 - 1 - 2` with edge factor `2` on agreement and `1` otherwise: the marginal of the
  last vertex is `9` for each value, and max-product decoding finds an assignment of weight at
  least `4`, the weight of the constant assignment.
-/

@[expose] public section

namespace Cslib.MachineLearning.BeliefPropagationTests

open Cslib.MachineLearning GraphicalModels Finset

/-- The two-vertex network `rain → wet` as a tree model. -/
noncomputable def rainTree : TreeModel Bool 1 where
  par _ := 0
  unary i a := if i = 0 then (if a then 1 / 5 else 4 / 5) else 1
  pair _ b a := if a then (if b then 9 / 10 else 1 / 10) else (if b then 1 / 10 else 9 / 10)

example : ∑ x with x 1 = true, rainTree.weight x = 13 / 50 := by
  rw [TreeModel.marginal_eq_belief, show (1 : Fin 2) = Fin.last 1 from rfl,
    TreeModel.belief_last, TreeModel.downMessage_apply]
  simp [TreeModel.belief, TreeModel.dropLast, TreeModel.lastParent, rainTree]
  norm_num

/-- The path `0 - 1 - 2` (vertex `2` has parent `1`), with edge factor `2` on agreement and `1`
on disagreement and unary factors `1`. -/
def path3 : TreeModel Bool 2 where
  par k := if h : (k : ℕ) = 0 then 0 else ⟨1, by omega⟩
  unary _ _ := 1
  pair _ b a := if b = a then 2 else 1

example (a : Bool) : ∑ x with x 2 = a, path3.weight x = 9 := by
  rw [TreeModel.marginal_eq_belief, show (2 : Fin 3) = Fin.last 2 from rfl,
    TreeModel.belief_last, TreeModel.downMessage_apply,
    show path3.lastParent = Fin.last 1 from rfl]
  simp only [TreeModel.belief_last, TreeModel.downMessage_apply]
  cases a <;>
    simp [TreeModel.belief, TreeModel.dropLast, TreeModel.lastParent, path3] <;> norm_num

theorem nonnegFactors_path3 : path3.NonnegFactors := by
  refine ⟨fun _ _ => zero_le_one, fun _ a b => ?_⟩
  simp only [path3]
  split_ifs <;> norm_num

example : 4 ≤ path3.weight path3.decode := by
  refine le_trans (le_of_eq ?_) (TreeModel.weight_le_weight_decode nonnegFactors_path3
    fun _ => true)
  simp [TreeModel.weight, path3]
  norm_num

end Cslib.MachineLearning.BeliefPropagationTests
