/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelector

/-!
# Obstruction to bondwise coordinate certificates

A bondwise coordinate certificate forces the toggle source to be empty at every contributing flux;
hence no certificate exists when the selector's actual mass on `s :: ss` is nonzero and the toggle
source `sourceClass(s :: ss) ∆ {s.1, s.2.1}` is nonempty.

## i. Overview

At a contributing flux, a labeled split of the left pair fiber exists; the two normal forms of a
certificate carry it to the right pair fiber, so the full current has both the source class of
`s :: ss` and the sources `{s.1, s.2.1}` of the active segment
(`BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes`). A nonzero actual mass
gives a contributing flux, so certificates are empty when the toggle source is nonempty
(`bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero`).

All results are proved unconditionally (under the stated nonvanishing hypotheses).

## ii. Key results

- `BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes` : a certificate forces
  an empty toggle source
- `bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero` : no certificate when the actual
  mass is nonzero and the toggle source is nonempty

## iii. Table of contents

- A. Labeled splits of nonzero pair masses
- B. Emptiness of bondwise coordinate certificates

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
noncomputable local instance certificateObstructionDecidableAdj
    (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching
open BackboneLabeledSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open FluxEdgeCopy

variable {D : Type*}

/-! ## A. Labeled splits of nonzero pair masses -/

/-- A nonzero raw source pair fiber mass has a labeled split of edge copies with the prescribed
sources and both fiber conditions. -/
lemma exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (hmass : rawSourcePairFiberMass G beta J m A Q R ≠ 0) :
    ∃ T : Finset (Copy G m),
      RandomCurrent.sources (endsM G m) T = A /\
        Q (profileFlux G m T) /\
        R (profileFlux G m (univ \ T)) := by
  classical
  by_contra hex
  apply hmass
  rw [rawSourcePairFiberMass_eq_labeled]
  unfold labeledSourcePairFiberMass
  apply Finset.sum_eq_zero
  intro T _
  exact (hex <| by
    exact ⟨T.1, T.2.1, T.2.2.1, T.2.2.2⟩).elim

/-! ## B. Emptiness of bondwise coordinate certificates -/

/-- A bondwise coordinate certificate forces the toggle source to be empty at a contributing
flux. -/
lemma BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V))
    (bit1 bit2 : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2
      bit1 bit2 S beta J d s ss hs)
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes S beta J d s ss hs m) :
    stepToggleSource S d s ss = ∅ := by
  change PairContributes d.graph beta J m
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss) at hm
  rcases hm with hleft | hright
  · obtain ⟨T, _, hfull, hvacuum⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m (S.sourceClass d (s :: ss))
          (S.Fiber d (s :: ss)) (liftedResidualVacuum d s) hleft
    have hnormal := (C.left_normal_form m (Or.inl hleft) T).mp
      ⟨hfull, hvacuum⟩
    have hhead := ((C.right_normal_form m (Or.inl hleft) T).mpr hnormal).1
    have hfullSources := S.sources_eq_sourceClass_of_select d
      (profileFlux d.graph m T) (s :: ss) hfull
    have heq : S.sourceClass d (s :: ss) = {s.1, s.2.1} :=
      hfullSources.symm.trans hhead.1
    simp [stepToggleSource, heq]
  · obtain ⟨T, _, hhead, hresidual⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (S.sourceClass d (s :: ss) ∆ stepToggleSource S d s ss)
          (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
          hright
    have hnormal := (C.right_normal_form m (Or.inr hright) T).mp
      ⟨hhead, hresidual⟩
    have hfull := ((C.left_normal_form m (Or.inr hright) T).mpr hnormal).1
    have hfullSources := S.sources_eq_sourceClass_of_select d
      (profileFlux d.graph m T) (s :: ss) hfull
    have heq : S.sourceClass d (s :: ss) = {s.1, s.2.1} :=
      hfullSources.symm.trans hhead.1
    simp [stepToggleSource, heq]

lemma BondwiseCoordinateCertificate.not_contributes_of_toggleSource_ne_empty
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V))
    (bit1 bit2 : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (C : BondwiseCoordinateCertificate X x accepted suffix1 suffix2
      bit1 bit2 S beta J d s ss hs)
    (hsource : stepToggleSource S d s ss ≠ ∅)
    (m : d.graph.edgeFinset -> Nat) :
    ¬ CoordinatePairContributes S beta J d s ss hs m := by
  intro hm
  exact hsource
    (BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes
      X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs C m hm)

lemma bondwiseCoordinateCertificate_isEmpty_of_contributes
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V))
    (bit1 bit2 : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes S beta J d s ss hs m)
    (hsource : stepToggleSource S d s ss ≠ ∅) :
    IsEmpty (BondwiseCoordinateCertificate X x accepted suffix1 suffix2
      bit1 bit2 S beta J d s ss hs) := by
  constructor
  intro C
  exact hsource
    (BondwiseCoordinateCertificate.stepToggleSource_eq_empty_of_contributes
      X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs C m hm)

/-- There is no bondwise coordinate certificate when the actual mass on `s :: ss` is nonzero and the
toggle source is nonempty. -/
theorem bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix1 suffix2 : List (Sym2 V))
    (bit1 bit2 : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hmass : S.actualMass beta J d (s :: ss) ≠ 0)
    (hsource : stepToggleSource S d s ss ≠ ∅) :
    IsEmpty (BondwiseCoordinateCertificate X x accepted suffix1 suffix2
      bit1 bit2 S beta J d s ss hs) := by
  have hvacuum :
      currentSum (shb_BackboneExplorationDomain.advance d s).graph
        beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos
      (shb_BackboneExplorationDomain.advance d s).graph beta J)
  have hleft : S.actualMass beta J d (s :: ss) *
      currentSum (shb_BackboneExplorationDomain.advance d s).graph
        beta J ∅ ≠ 0 := mul_ne_zero hmass hvacuum
  obtain ⟨m, hm⟩ := exists_contributing_of_left_ne_zero
    S beta J d s ss
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
    (partialActualMass_mul_residualCurrentSum_eq_pairTsum
      S beta J d s ss) hleft
  exact bondwiseCoordinateCertificate_isEmpty_of_contributes
    X x accepted suffix1 suffix2 bit1 bit2 S beta J d s ss hs
      m hm hsource

end BackboneConcreteSelector

end

end StatMech.Sharpness
