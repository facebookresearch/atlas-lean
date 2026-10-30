/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching

/-!
# Current dynamic selectors do not exist

The structure `shb_CurrentDynamicSelector` is empty as soon as `V` has two distinct vertices, so
every result quantifying over current dynamic selectors is vacuous. Also an edge-copy
multiplicity identity for a single edge at `β = J = 1`.

## i. Overview

Take the single-edge graph on `x ≠ y` with no active segments and the current with multiplicity
one on the edge. Its sources are `{x, y}`, nonempty. A current dynamic selector must select either
the empty word, whose source class is empty, or a word starting with a segment, which must be
active; both are impossible. This refutes the axioms of `shb_CurrentDynamicSelector`
(`shb_CurrentDynamicSelector_isEmpty_of_exists_ne`; for `V = Bool`,
`shb_no_CurrentDynamicSelector_bool`).

The last lemmas compute single-edge weights at `β = J = 1`: `w(0) w(2) = 1/2` and
`w(1) w(1) = 1`, so splitting two copies of an edge between two currents is weighted with
multiplicity two (`shb_singleEdge_edgeCopyMultiplicity_two`).

All results are proved unconditionally.

## ii. Key results

- `shb_CurrentDynamicSelector_isEmpty_of_exists_ne` : no current dynamic selector exists when `V`
  has two distinct vertices
- `shb_no_CurrentDynamicSelector_bool` : the case `V = Bool`
- `shb_singleEdge_edgeCopyMultiplicity_two` : `2 w(0) w(2) = w(1) w(1)` on a single edge

## iii. Table of contents

- A. The single-edge graph
- B. Emptiness of current dynamic selectors
- C. Edge-copy multiplicities on a single edge

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _

/-! ## A. The single-edge graph -/

/-- The graph on `V` with the single edge `{x, y}`. -/
def shb_singleEdgeGraph (x y : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(x, y)}

omit [DecidableEq V] in
lemma shb_singleEdgeGraph_edge_mem {x y : V} (hxy : x ≠ y) :
    s(x, y) ∈ (shb_singleEdgeGraph x y).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, shb_singleEdgeGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨Set.mem_singleton _, by
    simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using hxy⟩

omit [DecidableEq V] in
lemma shb_singleEdgeGraph_edgeFinset {x y : V} (hxy : x ≠ y) :
    (shb_singleEdgeGraph x y).edgeFinset = {s(x, y)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, shb_singleEdgeGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    subst e
    exact ⟨rfl, by simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using hxy⟩

/-- The exploration domain on the single-edge graph with no active segments. -/
def shb_emptyActiveSingleEdgeDomain (x y : V) : shb_ExplorationDomain V where
  graph := shb_singleEdgeGraph x y
  active := ∅
  active_supported := by simp

/-- The current with multiplicity one on the single edge. -/
def shb_singleEdgeFlux (x y : V) :
    (shb_emptyActiveSingleEdgeDomain x y).graph.edgeFinset -> Nat := fun _ => 1

lemma shb_singleEdgeFlux_incidentFlux_left {x y : V} (hxy : x ≠ y) :
    incidentFlux (shb_emptyActiveSingleEdgeDomain x y).graph
        (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
          (shb_singleEdgeFlux x y)) x = 1 := by
  unfold incidentFlux
  rw [show (shb_emptyActiveSingleEdgeDomain x y).graph.edgeFinset =
      {s(x, y)} by exact shb_singleEdgeGraph_edgeFinset hxy]
  have hfilter : ({s(x, y)} : Finset (Sym2 V)).filter (fun e => x ∈ e) =
      {s(x, y)} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro he
      subst e
      exact ⟨rfl, Sym2.mem_mk_left x y⟩
  rw [hfilter, Finset.sum_singleton]
  unfold ofEdgeFun shb_singleEdgeFlux
  rw [dite_eq_left]
  exact shb_singleEdgeGraph_edge_mem hxy

lemma shb_singleEdgeFlux_sources_ne_empty {x y : V} (hxy : x ≠ y) :
    sources (shb_emptyActiveSingleEdgeDomain x y).graph
        (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
          (shb_singleEdgeFlux x y)) ≠ ∅ := by
  intro hs
  have hx : x ∈ sources (shb_emptyActiveSingleEdgeDomain x y).graph
      (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph
        (shb_singleEdgeFlux x y)) := by
    rw [mem_sources, shb_singleEdgeFlux_incidentFlux_left hxy]
    exact odd_one
  rw [hs] at hx
  simp at hx

/-! ## B. Emptiness of current dynamic selectors -/

/-- There is no current dynamic selector when `V` has two distinct vertices: the single-edge
current on a domain without active segments has nonempty sources, so it can select neither the
empty word nor a word starting with a segment. -/
theorem shb_CurrentDynamicSelector_isEmpty_of_exists_ne
    (hne : ∃ x : V, ∃ y : V, x ≠ y) :
    IsEmpty (shb_CurrentDynamicSelector (V := V)) := by
  constructor
  intro S
  obtain ⟨x, y, hxy⟩ := hne
  let d := shb_emptyActiveSingleEdgeDomain x y
  let m := shb_singleEdgeFlux x y
  cases hword : S.select d m with
  | nil =>
      have hs := S.sources_eq_sourceClass_of_select d m [] hword
      rw [S.sourceClass_nil d] at hs
      exact shb_singleEdgeFlux_sources_ne_empty hxy hs
  | cons s ss =>
      have hsInactive : s ∉ d.active := by simp [d, shb_emptyActiveSingleEdgeDomain]
      exact S.select_ne_cons_of_not_active d s ss m hsInactive hword

/-- There is no current dynamic selector on `Bool`. -/
lemma shb_no_CurrentDynamicSelector_bool :
    IsEmpty (shb_CurrentDynamicSelector (V := Bool)) := by
  apply shb_CurrentDynamicSelector_isEmpty_of_exists_ne
  exact ⟨false, true, by decide⟩

/-! ## C. Edge-copy multiplicities on a single edge -/

/-- The current with constant multiplicity `k` on the single edge. -/
def shb_singleEdgeConstantFlux (x y : V) (k : Nat) :
    (shb_singleEdgeGraph x y).edgeFinset -> Nat := fun _ => k

lemma shb_singleEdge_rawSplit_zero_two {x y : V} (hxy : x ≠ y) :
    weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 0)) *
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 2)) = (1 / 2 : Real) := by
  have hadj : (shb_singleEdgeGraph x y).Adj x y := by
    rw [shb_singleEdgeGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_singleton _, hxy⟩
  unfold weight
  rw [shb_singleEdgeGraph_edgeFinset hxy]
  simp [ofEdgeFun, shb_singleEdgeConstantFlux, hadj]

lemma shb_singleEdge_rawSplit_one_one {x y : V} (hxy : x ≠ y) :
    weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 1)) *
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 1)) = (1 : Real) := by
  have hadj : (shb_singleEdgeGraph x y).Adj x y := by
    rw [shb_singleEdgeGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_singleton _, hxy⟩
  unfold weight
  rw [shb_singleEdgeGraph_edgeFinset hxy]
  simp [ofEdgeFun, shb_singleEdgeConstantFlux, hadj]

/-- On a single edge at `β = J = 1`, `2 w(0) w(2) = w(1) w(1)`. -/
lemma shb_singleEdge_edgeCopyMultiplicity_two {x y : V} (hxy : x ≠ y) :
    2 *
        (weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 0)) *
        weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 2))) =
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 1)) *
        weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 1)) := by
  rw [shb_singleEdge_rawSplit_zero_two hxy,
    shb_singleEdge_rawSplit_one_one hxy]
  norm_num

end

end StatMech.Sharpness
