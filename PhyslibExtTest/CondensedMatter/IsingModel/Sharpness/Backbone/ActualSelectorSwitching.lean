/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching`

* on one vertex (`Fin 1`) every current is sourceless, so the selector selecting the empty word
  everywhere is a `shb_CurrentDynamicSelector` (the structure is inhabited there; it is empty on
  two or more vertices, see `ActualSelectorObstruction`);
* `shb_CurrentDynamicSelector.actualMass_eq_generated` and
  `shb_currentDynamicSelector_actualMass_active` applied under the switching law;
* `shb_activeSegmentFiberMass_eq_segmentNum` (unconditional).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching

open _root_.StatMech _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _


/-- On one vertex every current has no sources. -/
theorem sources_fin1 (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] (n : Current (Fin 1)) :
    sources G n = ∅ := by
  have hG : G.edgeFinset = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp [Subsingleton.elim a b]
  simp [sources, incidentFlux, hG]

/-- The selector on one vertex that always selects the empty word. -/
noncomputable def unitSelector : shb_CurrentDynamicSelector (V := Fin 1) where
  sourceClass _ _ := ∅
  select _ _ := []
  sourceClass_nil _ := rfl
  sources_eq_sourceClass_of_select _ _ _ _ := sources_fin1 _ _
  select_nil_of_sources_empty _ _ _ := rfl
  select_ne_cons_of_not_active _ _ _ _ _ := (List.cons_ne_nil _ _).symm

-- Under the switching law, the actual fiber mass is the generated one.
example (β : ℝ) (J : Sym2 (Fin 1) → ℝ) (h : unitSelector.SwitchingLaw β J) :
    unitSelector.actualMass β J = shb_generatedExplorationFiberMass β J :=
  unitSelector.actualMass_eq_generated β J h

-- The active cut resummation identity under the switching law.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (S : shb_CurrentDynamicSelector)
    (β : ℝ) (J : Sym2 V → ℝ) (h : S.SwitchingLaw β J) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    S.actualMass β J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph β J ∅ =
      shb_segmentNum β J d s * S.actualMass β J (shb_BackboneExplorationDomain.advance d s) ss :=
  shb_currentDynamicSelector_actualMass_active S β J h d s ss hs

-- The active segment fiber mass is the segment numerator.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) (hs : s ∈ d.active) :
    (∑' m : d.graph.edgeFinset → ℕ,
      if shb_ActiveSegmentFiber d s hs m then shb_explorationCoordinateWeight β J d m else 0) =
      shb_segmentNum β J d s :=
  shb_activeSegmentFiberMass_eq_segmentNum β J d s hs

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching
