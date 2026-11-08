/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.VariableElimination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Tests for Bayesian networks and variable elimination

* A two-node network `rain → wet` on `Bool` with `P(rain) = 1/5`, `P(wet | rain) = 9/10`,
  `P(wet | no rain) = 1/10`: the joint of `(rain, wet)` is `9/50`, the joint is a distribution,
  the marginal of `rain` is `1/5`, and the conditional of `wet` given `rain` computed from the
  joint is `9/10`.
* The chain rule (`exists_chain`) instantiated on the uniform distribution of two bits.
* A star tree with root `0` and leaves `1, 2` on `Bool` with all factors `1`: variable
  elimination gives root messages `4` and partition function `8`.
* The path `0 - 1 - 2` (a non-root parent, depth two) with edge factors `2` on agreement and `1`
  otherwise: root messages `9`, partition function `18`.
* A two-vertex tree Bayesian network (prior `1/5` at the root, the table above on the edge):
  variable elimination recovers the prior as the root marginal.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModelsTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The distribution on `Bool` with `P(true) = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, StdSimplex.duple]

/-- `rain → wet`. -/
noncomputable def rainNet : BayesNet Bool 2 where
  pa k := if (k : ℕ) = 0 then ∅ else univ
  cpt k u := if h : (k : ℕ) = 0 then coin (1 / 5) (by norm_num) (by norm_num) else
    if u ⟨⟨0, Nat.pos_of_ne_zero h⟩, by simp [h]⟩ then coin (9 / 10) (by norm_num) (by norm_num)
    else coin (1 / 10) (by norm_num) (by norm_num)

example : rainNet.joint ![true, true] = 9 / 50 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_two]
  simp [rainNet, coin_true]
  norm_num

example : ∑ x, rainNet.joint x = 1 :=
  rainNet.sum_joint

theorem rain_marginal : rainNet.toChain.joint 1 ![true] = 1 / 5 := by
  simp [Chain.joint, BayesNet.toChain, rainNet, coin_true]

example : rainNet.toChain.joint 2 (Fin.snoc ![true] true) / rainNet.toChain.joint 1 ![true] =
    9 / 10 := by
  rw [rainNet.cond_eq_cpt (k := 1) (by norm_num) (by rw [rain_marginal]; norm_num)]
  simp [rainNet, coin_true]

/-- The chain rule on the uniform distribution of two bits. -/
example : ∃ c : Chain Bool, ∀ x : Fin 2 → Bool, (1 / 4 : ℝ) = c.joint 2 x :=
  exists_chain 2 (fun _ => 1 / 4) (fun _ => by norm_num) (by simp)

/-- The star with root `0` and leaves `1, 2`, all factors `1`. -/
def star : TreeModel Bool 2 where
  par _ := 0
  unary _ _ := 1
  pair _ _ _ := 1

theorem star_root (a : Bool) : star.rootMessage a = 4 := by
  simp [TreeModel.rootMessage, TreeModel.eliminate, TreeModel.message, TreeModel.lastParent, star]
  norm_num

example : ∑ x, star.weight x = 8 := by
  rw [TreeModel.partition_eq]
  simp [star_root]
  norm_num

/-- The path `0 - 1 - 2` (vertex `2` has parent `1`), with edge factor `2` on agreement and `1`
on disagreement and unary factors `1`. -/
def path3 : TreeModel Bool 2 where
  par k := if h : (k : ℕ) = 0 then 0 else ⟨1, by omega⟩
  unary _ _ := 1
  pair _ b a := if b = a then 2 else 1

theorem path3_root (a : Bool) : path3.rootMessage a = 9 := by
  cases a <;>
    simp [TreeModel.rootMessage, TreeModel.eliminate, TreeModel.message, TreeModel.lastParent,
      path3] <;> norm_num

example : ∑ x, path3.weight x = 18 := by
  rw [TreeModel.partition_eq]
  simp [path3_root]
  norm_num

/-- A tree Bayesian network on two vertices: prior `1/5` at the root and the table of `rainNet` on
the edge. -/
noncomputable def rainTree : TreeModel Bool 1 where
  par _ := 0
  unary i a := if i = 0 then (coin (1 / 5) (by norm_num) (by norm_num)).weights a else 1
  pair _ b a := (if a then coin (9 / 10) (by norm_num) (by norm_num)
    else coin (1 / 10) (by norm_num) (by norm_num)).weights b

example : ∑ x with x 0 = true, rainTree.weight x = 1 / 5 := by
  rw [TreeModel.rootMarginal_eq]
  simp [TreeModel.rootMessage, TreeModel.eliminate, TreeModel.message, TreeModel.lastParent,
    rainTree, coin_true, coin_false]

end Cslib.MachineLearning.GraphicalModelsTests
