/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.DecisionTreeReindex
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for reindexing decision trees

Tests for `CSLibExt.Complexity.BooleanFunctions.DecisionTreeReindex`, transporting the two-variable
`AND` tree `andTree` (over `Bool`) along the injective map `ι : Bool → Fin 3`,
`ι true = 0`, `ι false = 1`, which misses the coordinate `2`:

* `restrictConfig` and `DecisionTree.reindex` computed at small inputs (`decide`, `rfl`);
* `eval_reindex` and `evalR_reindex` at a concrete configuration of `Fin 3`;
* `queried_reindex` checked against a direct computation of both sides;
* `mem_queried_reindex_iff` with a proved injectivity hypothesis, and
  `not_mem_queried_reindex_of_not_range` for the coordinate `2` outside the range of `ι`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.DecisionTree

/-- The injective map `Bool → Fin 3` sending `true ↦ 0` and `false ↦ 1`. -/
def ιRe (b : Bool) : Fin 3 := if b then 0 else 1

/-- `ιRe` is injective. -/
lemma ιRe_injective : Function.Injective ιRe := by decide

/-- The coordinate `2` is not in the range of `ιRe`. -/
lemma two_not_mem_range_ιRe : (2 : Fin 3) ∉ Set.range ιRe := by
  rintro ⟨b, hb⟩
  cases b <;> simp [ιRe] at hb

/-! ## Definitions at small inputs -/

example : restrictConfig ιRe (fun i : Fin 3 => decide (i = 1)) = fun b => !b := by decide

example : andTree.reindex ιRe = .node 0 (.node 1 (.leaf true) (.leaf false)) (.leaf false) := rfl

example : (andTree.reindex ιRe).eval (fun i => decide (i ≠ 2)) = true := by decide
example : (andTree.reindex ιRe).queried (fun _ => true) = {0, 1} := by decide
example : (andTree.reindex ιRe).queried (fun i => decide (i = 1)) = {0} := by decide

/-! ## The reindexing lemmas -/

/-- `eval_reindex`: on the configuration `(true, false, true)` of `Fin 3`, the reindexed tree
evaluates like `andTree` on the restricted configuration, which is `false`. -/
example : (andTree.reindex ιRe).eval (fun i => decide (i ≠ 1)) = false := by
  rw [eval_reindex]; decide

example (ω : ConfigSpace (Fin 3)) :
    (andTree.reindex ιRe).evalR ω = andTree.evalR (restrictConfig ιRe ω) :=
  evalR_reindex ιRe andTree ω

/-- `queried_reindex`, checked against a direct computation of both sides. -/
example : (andTree.reindex ιRe).queried (fun _ => true)
    = (andTree.queried (restrictConfig ιRe fun _ => true)).image ιRe := by
  rw [queried_reindex]

example : (andTree.queried (restrictConfig ιRe fun _ => true)).image ιRe = {0, 1} := by decide

/-- `mem_queried_reindex_iff`: `ι false = 1` is queried on the all-true configuration because
`false` is queried by `andTree`. -/
example : ιRe false ∈ (andTree.reindex ιRe).queried (fun _ => true) :=
  (mem_queried_reindex_iff ιRe ιRe_injective andTree _ false).2 (by decide)

example (ω : ConfigSpace (Fin 3)) : (2 : Fin 3) ∉ (andTree.reindex ιRe).queried ω :=
  not_mem_queried_reindex_of_not_range ιRe andTree ω 2 two_not_mem_range_ιRe

end StatMechTest.BooleanFunctions
