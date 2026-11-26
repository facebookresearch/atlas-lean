/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelector

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelector`

* `no_functional_fiber_bridge_of_nonempty_event` (a refutation): no selector's fibers are the
  suffix events of a decoding that separates the empty bond list, once some event holds;
* `completeEvent_fluxEventOutsideCut` applied under its freshness hypotheses;
* `CompleteBondwiseSelectorSpec.toPartialSelector`: every complete specification determines a
  partial selector.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelector

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneConcreteSelector
open _root_.StatMech.Sharpness.BackboneDeterminedCutSwitching

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- No functional fiber bridge when some suffix event holds and the decoding separates `[]`.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {D : Type*}
    (S : shb_PartialCurrentDynamicSelector) (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : ℕ → Bool) (bonds : List (Sym2 V))
    (decode : List (Sym2 V) → List (shb_ExplorationSegment V)) (hdec : decode [] ≠ decode bonds)
    (hev : BondwiseSuffixEvent d.graph X x bonds bit m) :
    ¬ ∀ bs, S.Fiber d (decode bs) m ↔ BondwiseSuffixEvent d.graph X x bs bit m :=
  no_functional_fiber_bridge_of_nonempty_event S d m X x bit bonds decode hdec hev

-- Complete events inherit locality outside the cut from their terminal events.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) (x : P.State)
    (accepted : Sym2 V) (hinit : P.initial d = P.scan.advance x accepted)
    (hfresh : SuffixFresh P.scan x accepted (P.encode d word)) (m : d.graph.edgeFinset → ℕ)
    (ht : FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.TerminalEvent d word)) :
    FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.CompleteEvent d word) :=
  completeEvent_fluxEventOutsideCut P d word x accepted hinit hfresh m ht

-- A complete specification determines a partial selector.
noncomputable example {V : Type*} [Fintype V] [DecidableEq V] {P : BondwiseSegmentProgram V}
    (R : CompleteBondwiseSelectorSpec P) : shb_PartialCurrentDynamicSelector (V := V) :=
  R.toPartialSelector

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelector
