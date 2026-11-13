/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Sharpness.BackboneExplorationCutAdmissible

open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _







noncomputable def shb_cutLocalSourceSelector
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    (m : G.edgeFinset -> Nat) : Prop := by
  classical
  let ab := shb_cutEquiv G P m
  exact
    (sources G (ofEdgeFun G (shb_cutLeft G P ab.1)) = Aleft /\
      leftSelector ab.1) /\
    (sources G (ofEdgeFun G (shb_cutRight G P ab.2)) = Aright /\
      rightSelector ab.2)

noncomputable instance shb_cutLocalSourceSelector_decidable
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector] :
    DecidablePred
      (shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector) :=
  Classical.decPred _




theorem shb_cutLocalSourceSelector_admissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) :
    shb_LocalSourceSelectorAdmissible G P (Aleft ∆ Aright) Aleft Aright
      (shb_cutLocalSourceSelector G P Aleft Aright
        leftSelector rightSelector)
      leftSelector rightSelector := by
  classical
  intro a b
  have hab : shb_cutEquiv G P (shb_cutJoin G P (a, b)) = (a, b) :=
    (shb_cutEquiv G P).apply_symm_apply (a, b)
  constructor
  · rintro ⟨_, hselector⟩
    unfold shb_cutLocalSourceSelector at hselector
    dsimp only at hselector
    rw [hab] at hselector
    exact ⟨hselector.1, hselector.2⟩
  · rintro ⟨⟨hleftSource, hleft⟩, ⟨hrightSource, hright⟩⟩
    refine ⟨?_, ?_⟩
    · rw [shb_sources_cutJoin G P a b, hleftSource, hrightSource]
    · unfold shb_cutLocalSourceSelector
      dsimp only
      rw [hab]
      exact ⟨⟨hleftSource, hleft⟩, ⟨hrightSource, hright⟩⟩



theorem shb_cutLocalSourceSelectorMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector] :
    shb_cutFullPredicateMass G beta J
        (fun m => sources G (ofEdgeFun G m) = Aleft ∆ Aright /\
          shb_cutLocalSourceSelector G P Aleft Aright
            leftSelector rightSelector m) =
      shb_cutLeftPredicateMass G beta J P
          (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
            leftSelector a) *
        shb_cutRightPredicateMass G beta J P
          (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
            rightSelector b) := by
  exact shb_localSourceSelectorMass_factor G beta J P
    (Aleft ∆ Aright) Aleft Aright
    (shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector)
    leftSelector rightSelector
    (shb_cutLocalSourceSelector_admissible G P Aleft Aright
      leftSelector rightSelector)




theorem shb_dynamicSegmentCutLocalSelector_admissible
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (Aleft Aright : Finset V)
    (leftSelector :
      ({e : d.graph.edgeFinset // shb_segmentCut d.graph s e} -> Nat) -> Prop)
    (rightSelector :
      ({e : d.graph.edgeFinset // Not (shb_segmentCut d.graph s e)} -> Nat) -> Prop) :
    shb_LocalSourceSelectorAdmissible d.graph (shb_segmentCut d.graph s)
      (Aleft ∆ Aright) Aleft Aright
      (shb_cutLocalSourceSelector d.graph (shb_segmentCut d.graph s)
        Aleft Aright leftSelector rightSelector)
      leftSelector rightSelector :=
  shb_cutLocalSourceSelector_admissible d.graph
    (shb_segmentCut d.graph s) Aleft Aright leftSelector rightSelector






noncomputable def shb_actualExplorationFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)] :
    shb_ExplorationFiberMass V := fun d word =>
  ∑' m : d.graph.edgeFinset -> Nat,
    if sources d.graph (ofEdgeFun d.graph m) = sourceClass d word /\
        selector d word m then
      weight d.graph beta J (ofEdgeFun d.graph m)
    else 0





def shb_ActualExplorationFiberRealizes
    (beta : Real) (J : Sym2 V -> Real)
    (actualMass : shb_ExplorationFiberMass V) : Prop :=
  (forall d, actualMass d [] = currentSum d.graph beta J ∅) /\
  (forall d s ss, s ∈ d.active ->
    actualMass d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        actualMass (shb_BackboneExplorationDomain.advance d s) ss) /\
  (forall d s ss, s ∉ d.active -> actualMass d (s :: ss) = 0)



theorem shb_actualExplorationFiberMass_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector)) :
    shb_actualExplorationFiberMass beta J sourceClass selector =
      shb_generatedExplorationFiberMass beta J := by
  apply shb_LocalSelectorFiberCutResummation_unique beta J
  exact hrealizes




theorem shb_actualExplorationFiberRealizes_iff_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)] :
    shb_ActualExplorationFiberRealizes beta J
        (shb_actualExplorationFiberMass beta J sourceClass selector) <->
      shb_actualExplorationFiberMass beta J sourceClass selector =
        shb_generatedExplorationFiberMass beta J := by
  exact shb_LocalSelectorFiberCutResummation_iff_eq_generated beta J
    (shb_actualExplorationFiberMass beta J sourceClass selector)


theorem shb_actualExploration_rho_eq_weight
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector))
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho beta J
        (shb_actualExplorationFiberMass beta J sourceClass selector) d word =
      (shb_BackboneExplorationDomain.kernel beta J hbeta hJ hdom).weight
        d word := by
  exact shb_randomCurrent_rho_eq_weight beta J hbeta hJ hdom
    (shb_actualExplorationFiberMass beta J sourceClass selector)
    hrealizes d word




noncomputable def shb_actualExplorationRealization
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector)) :
    shb_ExplorationRhoRealization (shb_ExplorationDomain V)
      (shb_ExplorationSegment V) :=
  shb_randomCurrentExplorationRealization beta J hbeta hJ hdom
    (shb_actualExplorationFiberMass beta J sourceClass selector) hrealizes



theorem shb_actualExploration_P2
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector))
    (d : shb_ExplorationDomain V)
    (p q : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho beta J
        (shb_actualExplorationFiberMass beta J sourceClass selector)
        d (p ++ q) =
      shb_normalizedExplorationRho beta J
          (shb_actualExplorationFiberMass beta J sourceClass selector) d p *
        shb_normalizedExplorationRho beta J
          (shb_actualExplorationFiberMass beta J sourceClass selector)
          (shb_BackboneExplorationDomain.exploration.residual d p) q := by
  exact (shb_actualExplorationRealization beta J hbeta hJ hdom
    sourceClass selector hrealizes).P2 d p q

end

end StatMech.Sharpness
