/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.TreeComplete
public import CSLibExtTest.Complexity.BooleanFunctions.RevealmentConstruction

/-!
# Tests for the completed exploration tree

Tests for `CSLibExt.Complexity.BooleanFunctions.TreeComplete` on the path `0 — 1 — 2`
(`pathU`, `pathV`) and the lattice edge `s₀ — s₁` of `ℤ¹` from the `RevealmentConstruction`
tests:

* `repeatList`, `endpointsFinset` and `Saturated` at small inputs (`decide`), including a set
  that is not saturated;
* `runState_repeatList`, `runState_repeatList_saturated` and
  `mem_runState_repeatList_of_connOpenSet` on the path;
* `fixpoint_iterate_card` for the inflationary map `D ↦ D ∪ {0}` on `Fin 3`;
* non-vacuity of `eval_completeTree_iff` in both directions: the hypotheses (`l` lists every edge,
  `disc₀ = B = {2}`) hold, the completed tree is evaluated by `decide`, and the equivalence yields
  `ConnOpenSet` at the all-open configuration and its negation when the edge `1 — 2` is closed;
* `evalR_completeTree`, `connected_imp_reachOpen`, `connectedToSet_imp_connOpenSet` and
  `evalR_completeTree_connected` for the lattice edge, where the completed tree has value `1` on
  the all-open configuration.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.Lattice StatMech.OSSS StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.TreeComplete

example : repeatList [false, true] 2 = [false, true, false, true] := rfl
example : endpointsFinset pathU pathV [false, true] = {0, 1, 2} := by decide

example : Saturated pathU pathV (fun _ => true) [false, true] {0, 1, 2} := by
  unfold Saturated; decide
example : ¬ Saturated pathU pathV (fun _ => true) [false, true] {2} := by
  unfold Saturated; decide
example : Saturated pathU pathV (fun b => b) [false, true] {2} := by
  unfold Saturated; decide

/-- The list `[false, true]` contains every edge of the path. -/
lemma path_mem_list : ∀ e : Bool, e ∈ [false, true] := by decide

/-- The initial discovered set `{2}` lies in the target `{2}`. -/
lemma path_disc_sub : ∀ x ∈ ({2} : Finset (Fin 3)), x ∈ ({2} : Set (Fin 3)) := by simp

/-- The target `{2}` lies in the initial discovered set `{2}`. -/
lemma path_B_sub : ∀ b ∈ ({2} : Set (Fin 3)), b ∈ ({2} : Finset (Fin 3)) := by simp

example (ω : ConfigSpace Bool) :
    runState (geomGuard pathU pathV) (geomStep pathU pathV) ω (repeatList [false, true] 2) {2}
      = (fun D => runState (geomGuard pathU pathV) (geomStep pathU pathV) ω [false, true] D)^[2]
          {2} :=
  runState_repeatList pathU pathV ω _ 2 _

example (ω : ConfigSpace Bool) : Saturated pathU pathV ω [false, true]
    (runState (geomGuard pathU pathV) (geomStep pathU pathV) ω
      (repeatList [false, true] (({2} : Finset (Fin 3)) ∪ endpointsFinset pathU pathV
        [false, true]).card) {2}) :=
  runState_repeatList_saturated pathU pathV ω _ _

/-- `mem_runState_repeatList_of_connOpenSet`: on the all-open configuration the iterated run from
`2` discovers `0`. -/
example : (0 : Fin 3) ∈ runState (geomGuard pathU pathV) (geomStep pathU pathV) (fun _ => true)
    (repeatList [false, true] (({2} : Finset (Fin 3)) ∪ endpointsFinset pathU pathV
      [false, true]).card) {2} :=
  mem_runState_repeatList_of_connOpenSet pathU pathV _ _ path_mem_list {2} {2} path_B_sub
    connOpenSet_path_allOpen

example : (fun D : Finset (Fin 3) => D ∪ {0})
      ((fun D => D ∪ {0})^[(Finset.univ : Finset (Fin 3)).card] {2})
    = (fun D => D ∪ {0})^[(Finset.univ : Finset (Fin 3)).card] {2} :=
  fixpoint_iterate_card _ (Finset.univ : Finset (Fin 3)) (fun _ => Finset.subset_union_left)
    (fun _ _ => Finset.subset_univ _) _ (Finset.subset_univ _)

/-! ## The completed tree on the path -/

/-- The completed exploration tree of the path, from the target `{2}` towards the origin `0`. -/
noncomputable def pathComplete : DecisionTree Bool := completeTree pathU pathV 0 [false, true] {2}

/-- `eval_completeTree_iff` for the path: `pathComplete` decides whether `0` is connected to
`{2}`. -/
lemma pathComplete_iff (ω : ConfigSpace Bool) :
    pathComplete.eval ω = true ↔ ConnOpenSet pathU pathV ω 0 {2} :=
  eval_completeTree_iff pathU pathV 0 {2} _ path_mem_list {2} path_disc_sub path_B_sub ω

example : ConnOpenSet pathU pathV (fun _ => true) 0 {2} :=
  (pathComplete_iff _).1 (by decide)

/-- With the edge `1 — 2` closed, `0` is not connected to `2`; the completed tree decides it. -/
lemma not_connOpenSet_path_id : ¬ ConnOpenSet pathU pathV (fun b => b) 0 {2} := by
  rw [← pathComplete_iff]; decide

open scoped Classical in
example : pathComplete.evalR (fun _ => true) = 1 := by
  rw [pathComplete, evalR_completeTree pathU pathV 0 {2} _ path_mem_list {2} path_disc_sub
    path_B_sub]
  simp only [connOpenSet_path_allOpen, ↓reduceIte]

/-! ## The lattice edge `s₀ — s₁` -/

example : ReachOpen (fun _ : Unit => s₀) (fun _ => s₁) (fun _ => true) s₀ s₁ :=
  connected_imp_reachOpen latEdge_coh
    (reachOpen_imp_connected latEdge_injective latEdge_coh latAdj reachOpen_lat)

example : ConnOpenSet (fun _ : Unit => s₀) (fun _ => s₁) (fun _ => true) s₀ {s₁} :=
  connectedToSet_imp_connOpenSet latEdge_coh
    (connOpenSet_imp_connectedToSet latEdge_injective latEdge_coh latAdj ⟨s₁, rfl, reachOpen_lat⟩)

open scoped Classical in
/-- `evalR_completeTree_connected`: the completed tree for the lattice edge has value `1` on the
all-open configuration. -/
example : (completeTree (fun _ : Unit => s₀) (fun _ => s₁) s₀ [()] {s₁}).evalR (fun _ => true)
    = 1 := by
  have hc : ConnectedToSet 1 (liftCfg latEdge (fun _ => true)) s₀ ({s₁} : Set (Site 1)) :=
    connOpenSet_imp_connectedToSet latEdge_injective latEdge_coh latAdj ⟨s₁, rfl, reachOpen_lat⟩
  rw [evalR_completeTree_connected latEdge_injective latEdge_coh latAdj s₀ {s₁} [()]
    (fun _ => List.mem_singleton_self ()) {s₁} (fun x hx => by simpa using hx)
    (fun b hb => by simpa using hb)]
  simp only [hc, ↓reduceIte]

end StatMechTest.BooleanFunctions
