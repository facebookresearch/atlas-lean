/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.OSSS

/-!
# Tests for the OSSS inequality

Tests for `CSLibExt.Complexity.BooleanFunctions.OSSS` on the two-variable cube `{0, 1}^Bool`:

* the decision-tree semantics (`DecisionTree.eval`, `DecisionTree.queried`) on the dictator and
  the `AND` tree, by `decide`;
* the product-weight quantities `expect`, `var`, `cov`, `reveal`, `infl`, `condMean`, `flipAt`
  computed exactly for the Bernoulli(`1/2`) weight and an inhomogeneous weight;
* non-vacuity of `osss`, `osss_var` and `osss_bernoulli`: the hypothesis `IsProbWeight` holds for
  a homogeneous and an inhomogeneous weight, and the conclusions specialize to the explicit
  numerical inequalities `3/16 ≤ 3/4` and `3/8 ≤ 5/2`;
* `infl_indicator_eq_pivotal` and `expect_bernoulliWeight_eq_integral` at a concrete event.

The helper `sum_configSpace_bool` and the trees `dictTree`, `andTree` are reused by the other
test files of this directory.
-/

@[expose] public section


namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS

/-- A sum over the configurations of `{0, 1}^Bool`, as a double sum over the values at `true` and
at `false`. -/
lemma sum_configSpace_bool (g : ConfigSpace Bool → ℝ) :
    ∑ ω, g ω = ∑ a : Bool, ∑ b : Bool, g (fun x => cond x b a) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg g ?_
  funext x; cases x <;> simp [Equiv.boolArrowEquivProd]

/-- The dictator tree: query `true` and output its value. -/
def dictTree : DecisionTree Bool := .node true (.leaf true) (.leaf false)

/-- The `AND` tree: query `true`; if it is `true`, query `false` and output its value. -/
def andTree : DecisionTree Bool :=
  .node true (.node false (.leaf true) (.leaf false)) (.leaf false)

/-! ## Decision-tree semantics -/

example : dictTree.eval (fun x => x) = true := by decide
example : dictTree.eval (fun x => !x) = false := by decide
example : andTree.eval (fun _ => true) = true := by decide
example : andTree.eval (fun x => x) = false := by decide
example : andTree.queried (fun x => !x) = {true} := by decide
example : andTree.queried (fun _ => true) = {true, false} := by decide
example : (DecisionTree.leaf (E := Bool) true).queried (fun _ => true) = ∅ := by decide

lemma andTree_eval (ω : ConfigSpace Bool) : andTree.eval ω = (ω true && ω false) := by
  cases h₁ : ω true <;> cases h₂ : ω false <;> simp [andTree, DecisionTree.eval, h₁, h₂]

example : flipAt true (fun _ => true) = fun x => !x := by decide
example : pt true true = 1 ∧ pt true false = 0 := by simp [pt]

/-! ## Product-weight quantities at `p = 1/2` -/

/-- The uniform product weight on `{0, 1}^Bool`. -/
noncomputable abbrev νHalf : Bool → Bool → ℝ := bernoulliWeight (1 / 2)

lemma νHalf_isProbWeight : IsProbWeight νHalf :=
  bernoulliWeight_isProbWeight (by norm_num) (by norm_num)

example : weight νHalf (fun _ => true) = 1 / 4 := by
  simp [weight, bernoulliWeight]; norm_num

lemma expect_andTree : expect νHalf andTree.evalR = 1 / 4 := by
  simp [expect, weight, sum_configSpace_bool, andTree, DecisionTree.evalR, DecisionTree.eval,
    bernoulliWeight]
  norm_num

lemma var_andTree : var νHalf andTree.evalR = 3 / 16 := by
  simp [var, cov, expect, weight, sum_configSpace_bool, andTree, DecisionTree.evalR,
    DecisionTree.eval, bernoulliWeight]
  norm_num

lemma reveal_andTree_true : reveal νHalf andTree true = 1 :=
  reveal_root νHalf_isProbWeight _ _ _

lemma reveal_andTree_false : reveal νHalf andTree false = 1 / 2 := by
  simp [reveal, expect, weight, sum_configSpace_bool, andTree, DecisionTree.queried,
    bernoulliWeight]
  norm_num

lemma infl_andTree (e : Bool) : infl νHalf andTree.evalR e = 1 / 2 := by
  cases e <;>
  · simp [infl, expect, weight, sum_configSpace_bool, andTree, DecisionTree.evalR,
      DecisionTree.eval, bernoulliWeight, setOpen, setClosed]
    norm_num

example : reveal νHalf dictTree false = 0 := by
  simp [reveal, expect, weight, dictTree, DecisionTree.queried]

example : infl νHalf dictTree.evalR true = 1 := by
  simp [infl, expect, weight, sum_configSpace_bool, dictTree, DecisionTree.evalR,
    DecisionTree.eval, bernoulliWeight, setOpen, setClosed]
  norm_num

example (ω : ConfigSpace Bool) :
    condMean νHalf true andTree.evalR ω = if ω false then 1 / 2 else 0 := by
  cases h : ω false <;>
    simp [condMean, andTree, DecisionTree.evalR, DecisionTree.eval, bernoulliWeight, setOpen,
      setClosed, h]

/-! ## Non-vacuity of the OSSS inequality -/

/-- `osss_var` for the `AND` tree at `p = 1/2` is the inequality `3/16 ≤ 1 · 1/2 + 1/2 · 1/2`. -/
example : (3 / 16 : ℝ) ≤ 3 / 4 := by
  have h := osss_var νHalf_isProbWeight andTree
  rw [var_andTree, Fintype.sum_bool, reveal_andTree_true, reveal_andTree_false, infl_andTree,
    infl_andTree] at h
  linarith

/-- A real test function: `g ω = 2 · ω(true) + ω(false)`. -/
noncomputable def gLin (ω : ConfigSpace Bool) : ℝ :=
  (if ω true then 2 else 0) + if ω false then 1 else 0

lemma cov_andTree_gLin : cov νHalf andTree.evalR gLin = 3 / 8 := by
  simp [cov, expect, weight, sum_configSpace_bool, andTree, DecisionTree.evalR, DecisionTree.eval,
    bernoulliWeight, gLin]
  norm_num

lemma infl_gLin_true : infl νHalf gLin true = 2 := by
  simp [infl, expect, weight, sum_configSpace_bool, bernoulliWeight, gLin, setOpen, setClosed]
  norm_num

lemma infl_gLin_false : infl νHalf gLin false = 1 := by
  simp [infl, expect, weight, sum_configSpace_bool, bernoulliWeight, gLin, setOpen, setClosed]
  norm_num

/-- `osss` (covariance form) for the `AND` tree and `gLin`: `3/8 ≤ 1 · 2 + 1/2 · 1`. -/
example : (3 / 8 : ℝ) ≤ 5 / 2 := by
  have h := osss νHalf_isProbWeight andTree gLin
  rw [cov_andTree_gLin, Fintype.sum_bool, reveal_andTree_true, reveal_andTree_false,
    infl_gLin_true, infl_gLin_false] at h
  linarith

/-- `osss_bernoulli` applies at every `p ∈ [0, 1]`, including the endpoints. -/
example (g : ConfigSpace Bool → ℝ) :
    cov (bernoulliWeight 0) andTree.evalR g
      ≤ ∑ i, reveal (bernoulliWeight 0) andTree i * infl (bernoulliWeight 0) g i :=
  osss_bernoulli le_rfl zero_le_one andTree g

/-- An inhomogeneous product weight: coordinate `true` is `1` with probability `1/3`, coordinate
`false` with probability `3/4`. -/
noncomputable def νInh : Bool → Bool → ℝ := fun e b =>
  if e then (if b then 1 / 3 else 2 / 3) else (if b then 3 / 4 else 1 / 4)

lemma νInh_isProbWeight : IsProbWeight νInh where
  nonneg e b := by cases e <;> cases b <;> norm_num [νInh]
  normalized e := by cases e <;> norm_num [νInh]

example : expect νInh andTree.evalR = 1 / 4 := by
  simp [expect, weight, sum_configSpace_bool, andTree, DecisionTree.evalR, DecisionTree.eval,
    νInh]
  norm_num

example : reveal νInh andTree false = 1 / 3 := by
  simp [reveal, expect, weight, sum_configSpace_bool, andTree, DecisionTree.queried, νInh]
  norm_num

/-- `osss` holds for the inhomogeneous weight. -/
example : cov νInh andTree.evalR gLin ≤ ∑ i, reveal νInh andTree i * infl νInh gLin i :=
  osss νInh_isProbWeight andTree gLin

/-! ## Influences of events and the measure-theoretic expectation -/

/-- The event `{ω | ω true ∧ ω false}` computed by `andTree`. -/
def andEvent : Set (ConfigSpace Bool) := {ω | ω true = true ∧ ω false = true}

example : infl νHalf (andEvent.indicator fun _ => (1 : ℝ)) true
    = expect νHalf ({ω | IsPivotal true andEvent ω}.indicator fun _ => (1 : ℝ)) :=
  infl_indicator_eq_pivotal νHalf andEvent true

/-- `true` is pivotal for `andEvent` exactly when `ω false = true`. -/
example (ω : ConfigSpace Bool) : IsPivotal true andEvent ω ↔ ω false = true := by
  simp [IsPivotal, andEvent, setOpen, setClosed, ]

open MeasureTheory in
example :
    ∫ ω, andTree.evalR ω ∂(bernoulliProductMeasure (E := Bool) (1 / 2) (by norm_num)) = 1 / 4 := by
  rw [← expect_bernoulliWeight_eq_integral, show ((1 / 2 : NNReal) : ℝ) = 1 / 2 by norm_num]
  exact expect_andTree

end StatMechTest.BooleanFunctions
