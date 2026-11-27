/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelectorAdmissible

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelectorAdmissible`

* `shb_cutLocalSourceSelector_admissible` and `shb_cutLocalSourceSelectorMass_factor`
  (unconditional) for any cut and side selectors;
* `shb_actualExplorationFiberRealizes_iff_eq_generated` applied;
* `shb_actualExploration_P2` applied under `LocalDomainResummation` and realization.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelectorAdmissible

open _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The cut-local source selector is admissible.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V)
    (P : G.edgeFinset → Prop) [DecidablePred P] (Al Ar : Finset V)
    (ls : ({ e // P e } → ℕ) → Prop) (rs : ({ e // ¬ P e } → ℕ) → Prop) :
    shb_LocalSourceSelectorAdmissible G P (symmDiff Al Ar) Al Ar
      (shb_cutLocalSourceSelector G P Al Ar ls rs) ls rs :=
  shb_cutLocalSourceSelector_admissible G P Al Ar ls rs

-- Its mass factorizes.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (P : G.edgeFinset → Prop) [DecidablePred P] (Al Ar : Finset V)
    (ls : ({ e // P e } → ℕ) → Prop) [DecidablePred ls]
    (rs : ({ e // ¬ P e } → ℕ) → Prop) [DecidablePred rs] :=
  shb_cutLocalSourceSelectorMass_factor G β J P Al Ar ls rs

-- Realization is equality with the generated fiber mass.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (sc : shb_ExplorationDomain V → List (shb_ExplorationSegment V) → Finset V)
    (sel : (d : shb_ExplorationDomain V) → List (shb_ExplorationSegment V) →
      (d.graph.edgeFinset → ℕ) → Prop) [∀ d w, DecidablePred (sel d w)] :=
  shb_actualExplorationFiberRealizes_iff_eq_generated β J sc sel

-- The chain rule for a realizing selector.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (sc : shb_ExplorationDomain V → List (shb_ExplorationSegment V) → Finset V)
    (sel : (d : shb_ExplorationDomain V) → List (shb_ExplorationSegment V) →
      (d.graph.edgeFinset → ℕ) → Prop) [∀ d w, DecidablePred (sel d w)]
    (h : shb_ActualExplorationFiberRealizes β J (shb_actualExplorationFiberMass β J sc sel)) :=
  shb_actualExploration_P2 β J hβ hJ hdom sc sel h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelectorAdmissible
