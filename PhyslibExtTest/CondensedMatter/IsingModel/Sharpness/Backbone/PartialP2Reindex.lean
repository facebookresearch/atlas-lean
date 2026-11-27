/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialP2Reindex

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialP2Reindex`

* `rawSourcePairFiberMass_eq_of_labeledToggle` applied under its toggle hypothesis;
* `clearedP2_iff_pairMass_tsum_eq`: once both sides are reindexed, the active identity is an
  equality of pair-mass sums;
* `actualMass_active_of_contributingToggle` applied (the conditional P2 route).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.PartialP2Reindex

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneLabeledSwitching
open _root_.StatMech.Sharpness.BackboneDeterminedCutSwitching
open _root_.StatMech.Sharpness.shb_PartialCurrentDynamicSelector
open _root_.StatMech.Sharpness.BackbonePartialP2Reindex

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Labeled toggles preserve source-pair fiber masses.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (m : G.edgeFinset → ℕ) (A C : Finset V) (P : Finset (FluxEdgeCopy.Copy G m))
    (hP : RandomCurrent.sources (FluxEdgeCopy.endsM G m) P = C)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset → ℕ) → Prop) [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] :=
  rawSourcePairFiberMass_eq_of_labeledToggle G β J m A C P hP Q₁ R₁ Q₂ R₂

-- The cleared P2 identity as an equality of pair sums.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector (V := V)) (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset → ℕ) → Prop) [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] :=
  BackbonePartialP2Reindex.clearedP2_iff_pairMass_tsum_eq S β J d s ss A C Q₁ R₁ Q₂ R₂

-- The active identity from a contributing toggle.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector (V := V)) (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset → ℕ) → Prop) [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] :=
  BackbonePartialP2Reindex.actualMass_active_of_contributingToggle S β J d s ss A C Q₁ R₁ Q₂ R₂

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.PartialP2Reindex
