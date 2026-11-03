/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelectorObstruction

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelectorObstruction`

* `bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero` (refutation): no bondwise
  coordinate certificate exists when the actual mass and the toggle source are nonzero;
* `BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes`: a certificate with a
  contributing pair forces an empty toggle source;
* the two combine: a certificate and a contributing pair rule out a nonempty toggle source.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelectorObstruction

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneConcreteSelector
open _root_.StatMech.Sharpness.BackboneP2CoordinateReindex

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- No certificate when the actual mass and the toggle source are nonzero.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {D : Type*}
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D) (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V)) (bit1 bit2 : ℕ → Bool)
    (S : shb_PartialCurrentDynamicSelector) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hmass : S.actualMass β J d (s :: ss) ≠ 0) (hsrc : stepToggleSource S d s ss ≠ ∅) :
    IsEmpty
      (BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S β J d s ss hs) :=
  bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero X x accepted suffix1 suffix2 bit1
    bit2 S β J d s ss hs hmass hsrc

-- A certificate with a contributing pair has an empty toggle source.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {D : Type*}
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D) (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V)) (bit1 bit2 : ℕ → Bool)
    (S : shb_PartialCurrentDynamicSelector) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S β J d s ss hs)
    (m : d.graph.edgeFinset → ℕ) (hm : CoordinatePairContributes S β J d s ss hs m) :
    stepToggleSource S d s ss = ∅ :=
  BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes X x accepted suffix1
    suffix2 bit1 bit2 S β J d s ss hs C m hm

-- Hence a certificate, a contributing pair and a nonempty toggle source are incompatible.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {D : Type*}
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D) (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V)) (bit1 bit2 : ℕ → Bool)
    (S : shb_PartialCurrentDynamicSelector) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2 bit1 bit2 S β J d s ss hs)
    (m : d.graph.edgeFinset → ℕ) (hm : CoordinatePairContributes S β J d s ss hs m)
    (hsrc : stepToggleSource S d s ss ≠ ∅) : False :=
  hsrc (BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes X x accepted
    suffix1 suffix2 bit1 bit2 S β J d s ss hs C m hm)

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelectorObstruction
