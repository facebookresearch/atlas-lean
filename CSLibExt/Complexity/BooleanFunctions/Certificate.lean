/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.BooleanFunctions.OSSS

/-!
# Certificates from decision-tree computation paths

For a decision tree `T : StatMech.OSSS.DecisionTree E` and an input `ω`, the variables
`T.queried ω` read on the computation path of `ω` form a certificate for `T` at `ω`: every input
that agrees with `ω` on them evaluates like `ω`. There are at most `T.depth` of them, where the
depth is the number of queries on a longest root-to-leaf path.

If `T` computes a Boolean function `f`, then `T.queried ω` is a certificate for `f` at `ω` with at
most `T.depth` variables. This is the pointwise fact behind the inequality `C(f) ≤ D(f)` between
certificate complexity and decision-tree depth; neither complexity measure is defined here.

The archived development in `Atlas/StatisticalMechanics/Code/OSSS`, which stays outside the root
build, states the same two facts as `Revealment.card_queried_le_depth` and
`Coding.eval_eq_of_agree_on_queried`.

## Main definitions

* `StatMech.OSSS.DecisionTree.depth`: the depth of a decision tree.

## Main results

* `StatMech.OSSS.DecisionTree.card_queried_le_depth`: at most `T.depth` variables are queried on
  any input.
* `StatMech.OSSS.DecisionTree.eval_eq_of_agree_on_queried`: an input that agrees with `ω` on
  `T.queried ω` evaluates like `ω`.
-/

@[expose] public section

namespace StatMech.OSSS.DecisionTree

variable {E : Type*}

/-- The depth of a decision tree: the number of queries on a longest root-to-leaf path. -/
def depth : DecisionTree E → ℕ
  | leaf _ => 0
  | node _ t f => 1 + max t.depth f.depth

variable [DecidableEq E]

/-- At most `T.depth` variables are queried on any input. A variable queried twice on the
computation path counts once, so the bound can be strict. -/
theorem card_queried_le_depth (T : DecisionTree E) (ω : ConfigSpace E) :
    (T.queried ω).card ≤ T.depth := by
  induction T with
  | leaf b => simp [queried, depth]
  | node e t f iht ihf =>
    rw [queried, depth]
    refine (Finset.card_insert_le _ _).trans ?_
    split
    · have := le_max_left t.depth f.depth
      omega
    · have := le_max_right t.depth f.depth
      omega

/-- **The computation path is a certificate.** An input `ω'` that agrees with `ω` on the variables
`T.queried ω` queried on input `ω` evaluates like `ω`. -/
theorem eval_eq_of_agree_on_queried (T : DecisionTree E) (ω ω' : ConfigSpace E)
    (h : ∀ e ∈ T.queried ω, ω' e = ω e) : T.eval ω' = T.eval ω := by
  induction T with
  | leaf b => rfl
  | node e t f iht ihf =>
    rw [queried] at h
    have he : ω' e = ω e := h e (Finset.mem_insert_self _ _)
    have hsub : ∀ i ∈ (if ω e then t.queried ω else f.queried ω), ω' i = ω i :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [eval, eval, he]
    cases hω : ω e
    · rw [hω] at hsub
      exact ihf hsub
    · rw [hω] at hsub
      exact iht hsub

end StatMech.OSSS.DecisionTree
