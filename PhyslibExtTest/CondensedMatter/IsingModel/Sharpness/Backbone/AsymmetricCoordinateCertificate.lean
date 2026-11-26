/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.AsymmetricCoordinateCertificate

/-!
# Tests for `AsymmetricCoordinateCertificate`

Module under test:
`PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.AsymmetricCoordinateCertificate`.

* `BondwiseRunSpec.ofPredicate_event`: on `K₂`, the predicate "every edge has even flux" is the
  event of a run specification (evaluated at the zero flux);
* `BondwisePairEvent.toggle_iff_of_componentwise` applied to two covariances;
* `CompleteBondwiseSelectorSpec.not_toggleExists_of_activeIdentity_ne` (the obstruction) and
  `nonempty_canonicalCertificate_iff_toggleExists` applied to any complete specification.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone
namespace AsymmetricCoordinateCertificate

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneConcreteSelector

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Every predicate on fluxes is a run event: here "all fluxes even" at the zero flux on `K₂`.
example : (BondwiseRunSpec.ofPredicate (⊤ : SimpleGraph (Fin 2))
    (fun m => ∀ e, Even (m e))).Event ⊤ (fun _ => 0) :=
  (BondwiseRunSpec.ofPredicate_event _ _ _).mpr fun _ => ⟨0, rfl⟩

-- Componentwise covariance gives a pair toggle.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (l₁ l₂ r₁ r₂ : BondwiseRunSpec V) (G : SimpleGraph V) (m : G.edgeFinset → ℕ)
    (path : Finset (FluxEdgeCopy.Copy G m)) (h₁ : BondwiseRunToggleCovariance l₁ r₁ G m path)
    (h₂ : BondwiseRunToggleCovariance l₂ r₂ G m path) (T : Finset (FluxEdgeCopy.Copy G m)) :
    BondwisePairEvent l₁ l₂ G m T ↔ BondwisePairEvent r₁ r₂ G m (symmDiff T path) :=
  BondwisePairEvent.toggle_iff_of_componentwise l₁ l₂ r₁ r₂ G m path h₁ h₂ T

-- The canonical toggle cannot exist when the active identity fails.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {P : BondwiseSegmentProgram V}
    (R : CompleteBondwiseSelectorSpec P) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hne : R.toPartialSelector.actualMass β J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph β J ∅ ≠
      shb_segmentNum β J d s *
        R.toPartialSelector.actualMass β J (shb_BackboneExplorationDomain.advance d s) ss) :
    ¬ R.CanonicalBondwiseToggleExists β J d s ss hs :=
  R.not_toggleExists_of_activeIdentity_ne β J d s ss hs hne

-- Canonical certificates exist exactly when canonical toggles do.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {P : BondwiseSegmentProgram V}
    (R : CompleteBondwiseSelectorSpec P) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :=
  R.nonempty_canonicalCertificate_iff_toggleExists β J d s ss hs

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.AsymmetricCoordinateCertificate
