/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.BackboneBondwiseOrderedExploration

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable local instance partialSelectorP2DecidableAdj
    (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

namespace BackboneLabeledSwitching

open FluxEdgeCopy
open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def rawSourcePairFiberMass (beta : Real)
    (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  rawPairFiberMass G beta J m
    (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) R



noncomputable def labeledSourcePairFiberMass (beta : Real)
    (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  ∑ S : Fiber G m A (fun S =>
      Q (profileFlux G m S) ∧ R (profileFlux G m (univ \ S))),
    labeledWeight G beta J m S.1



theorem rawSourcePairFiberMass_eq_labeled
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] :
    rawSourcePairFiberMass G beta J m A Q R =
      labeledSourcePairFiberMass G beta J m A Q R := by
  classical
  rw [show rawSourcePairFiberMass G beta J m A Q R =
      ∑ K : {p : G.edgeFinset -> Nat // p <= m},
        if sources G (ofEdgeFun G K.1) = A ∧ Q K.1 ∧
            R (fun e => m e - K.1 e) then
          rawSplitWeight G beta J m K else 0 by
    unfold rawSourcePairFiberMass rawPairFiberMass
    apply Finset.sum_congr rfl
    intro K _
    simp only [and_assoc]]
  rw [rawPredicateMass_eq_labeled G beta J m
    (fun k => sources G (ofEdgeFun G k) = A ∧ Q k ∧
      R (fun e => m e - k e))]
  unfold labeledSourcePairFiberMass
  have hsubtype :
      (∑ S : Finset (FluxEdgeCopy.Copy G m),
        if RandomCurrent.sources (endsM G m) S = A ∧
            Q (profileFlux G m S) ∧
            R (profileFlux G m (univ \ S)) then
          labeledWeight G beta J m S else 0) =
        ∑ S : Fiber G m A (fun S =>
            Q (profileFlux G m S) ∧
              R (profileFlux G m (univ \ S))),
          labeledWeight G beta J m S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  rw [← hsubtype]
  apply Finset.sum_congr rfl
  intro S _
  rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_compl]




theorem rawSourcePairFiberMass_eq_of_labeledToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (htransport : ∀ S,
      (Q₁ (profileFlux G m S) ∧
          R₁ (profileFlux G m (univ \ S))) <->
        (Q₂ (profileFlux G m (S ∆ P)) ∧
          R₂ (profileFlux G m (univ \ (S ∆ P))))) :
    rawSourcePairFiberMass G beta J m A Q₁ R₁ =
      rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
  rw [rawSourcePairFiberMass_eq_labeled G beta J m A Q₁ R₁,
    rawSourcePairFiberMass_eq_labeled G beta J m (A ∆ C) Q₂ R₂]
  exact sum_labeledWeight_toggle G beta J m A C P hPsrc
    (fun S => Q₁ (profileFlux G m S) ∧
      R₁ (profileFlux G m (univ \ S)))
    (fun S => Q₂ (profileFlux G m S) ∧
      R₂ (profileFlux G m (univ \ S))) htransport

end BackboneLabeledSwitching

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem compl_symmDiff (m : G.edgeFinset -> Nat)
    (S P : Finset (FluxEdgeCopy.Copy G m)) :
    univ \ (S ∆ P) = (univ \ S) ∆ P := by
  classical
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  tauto




theorem pairTransport_of_fluxEventsOutsideCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    (hQ : FluxEventOutsideCut G m cut Q)
    (hR : FluxEventOutsideCut G m cut R)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P)
    (S : Finset (FluxEdgeCopy.Copy G m)) :
    (Q (profileFlux G m S) ∧
        R (profileFlux G m (univ \ S))) <->
      (Q (profileFlux G m (S ∆ P)) ∧
        R (profileFlux G m (univ \ (S ∆ P)))) := by
  have hQt := fluxEvent_toggle_iff G m cut Q hQ S P hP
  have hRt := fluxEvent_toggle_iff G m cut R hR (univ \ S) P hP
  rw [compl_symmDiff G m S P]
  exact and_congr hQt hRt



theorem rawSourcePairFiberMass_eq_of_determinedCutToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m cut P)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (hQ : FluxEventOutsideCut G m cut Q)
    (hR : FluxEventOutsideCut G m cut R) :
    BackboneLabeledSwitching.rawSourcePairFiberMass
        G beta J m A Q R =
      BackboneLabeledSwitching.rawSourcePairFiberMass
        G beta J m (A ∆ C) Q R := by
  apply BackboneLabeledSwitching.rawSourcePairFiberMass_eq_of_labeledToggle
    G beta J m A C P hPsrc Q R Q R
  exact pairTransport_of_fluxEventsOutsideCut G m cut Q R hQ hR P hPcut

end BackboneDeterminedCutSwitching



namespace shb_PartialCurrentDynamicSelector



noncomputable def actualMass
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V :=
  fun d word =>
    ∑' m : d.graph.edgeFinset -> Nat,
      if S.Fiber d word m then weight d.graph beta J (ofEdgeFun d.graph m)
      else 0


theorem actualMass_nil
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) (d : shb_ExplorationDomain V) :
    S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
  unfold actualMass currentSum shb_PartialCurrentDynamicSelector.Fiber
  apply tsum_congr
  intro m
  by_cases hsrc : sources d.graph (ofEdgeFun d.graph m) = ∅
  · have hselect : S.select? d m = some [] :=
      (S.select?_eq_some_nil_iff d m).2 hsrc
    simp [hsrc, hselect]
  · have hselect : S.select? d m ≠ some [] := fun h =>
      hsrc ((S.select?_eq_some_nil_iff d m).1 h)
    simp [hsrc, hselect]

end shb_PartialCurrentDynamicSelector



namespace BackbonePartialP2Reindex

open FluxEdgeCopy
open BackboneLabeledSwitching
open BackboneDeterminedCutSwitching

variable {D : Type*}

noncomputable local instance partialP2DecidableAdj (H : SimpleGraph V) :
    DecidableRel H.Adj := Classical.decRel _



def PairContributes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat)
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] : Prop :=
  rawSourcePairFiberMass G beta J m A Q₁ R₁ ≠ 0 ∨
    rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ ≠ 0




abbrev ContributingPathSelector
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] :=
  ∀ m : G.edgeFinset -> Nat,
    PairContributes G beta J m A C Q₁ R₁ Q₂ R₂ ->
      Finset (FluxEdgeCopy.Copy G m)



theorem pairMass_eq_of_contributingToggle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (transport : ∀ m hm S,
      (Q₁ (profileFlux G m S) ∧
          R₁ (profileFlux G m (univ \ S))) <->
        (Q₂ (profileFlux G m (S ∆ path m hm)) ∧
          R₂ (profileFlux G m (univ \ (S ∆ path m hm)))))
    (m : G.edgeFinset -> Nat) :
    rawSourcePairFiberMass G beta J m A Q₁ R₁ =
      rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
  by_cases hm : PairContributes G beta J m A C Q₁ R₁ Q₂ R₂
  · exact rawSourcePairFiberMass_eq_of_labeledToggle G beta J m A C
      (path m hm) (path_sources m hm) Q₁ R₁ Q₂ R₂ (transport m hm)
  · unfold PairContributes at hm
    rw [not_or] at hm
    exact (not_ne_iff.mp hm.1).trans (not_ne_iff.mp hm.2).symm




theorem source_eq_empty_of_zero_contributes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (hzero : PairContributes G beta J (fun _ => 0)
      A C Q₁ R₁ Q₂ R₂) :
    C = ∅ := by
  let m0 : G.edgeFinset -> Nat := fun _ => 0
  have hcopies : path m0 hzero = ∅ := by
    ext i
    exact Fin.elim0 i.2
  calc
    C = RandomCurrent.sources (endsM G m0) (path m0 hzero) :=
      (path_sources m0 hzero).symm
    _ = RandomCurrent.sources (endsM G m0) ∅ := by rw [hcopies]
    _ = ∅ := by
      ext v
      simp [RandomCurrent.mem_sources, RandomCurrent.degK]




theorem zero_not_contributes_of_source_ne_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (hC : C ≠ ∅) :
    ¬PairContributes G beta J (fun _ => 0) A C Q₁ R₁ Q₂ R₂ := by
  intro hzero
  exact hC (source_eq_empty_of_zero_contributes G beta J A C
    Q₁ R₁ Q₂ R₂ path path_sources hzero)




theorem clearedP2_iff_pairMass_tsum_eq
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) :
    (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) <->
      ((∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
  rw [left_reindex, right_reindex]




theorem actualMass_active_of_contributingToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂)
    (path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (transport : ∀ m hm T,
      (Q₁ (profileFlux d.graph m T) ∧
          R₁ (profileFlux d.graph m (univ \ T))) <->
        (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧
          R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  rw [left_reindex, right_reindex]
  apply tsum_congr
  exact pairMass_eq_of_contributingToggle d.graph beta J A C
    Q₁ R₁ Q₂ R₂ path path_sources transport




theorem actualMass_active_of_contributingDeterminedToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V) (cut : Set (Sym2 V))
    (Q R : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q R)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q R)
    (path : ContributingPathSelector d.graph beta J A C Q R Q R)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (path_supported : ∀ m hm,
      SupportedInCut d.graph m cut (path m hm))
    (hQ : ∀ m, PairContributes d.graph beta J m A C Q R Q R ->
      FluxEventOutsideCut d.graph m cut Q)
    (hR : ∀ m, PairContributes d.graph beta J m A C Q R Q R ->
      FluxEventOutsideCut d.graph m cut R) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  apply actualMass_active_of_contributingToggle S beta J d s ss A C
    Q R Q R left_reindex right_reindex path path_sources
  intro m hm T
  exact pairTransport_of_fluxEventsOutsideCut d.graph m cut Q R
    (hQ m hm) (hR m hm) (path m hm) (path_supported m hm) T



theorem exists_contributing_of_left_ne_zero
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (hleft : S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ ≠ 0) :
    ∃ m, PairContributes d.graph beta J m A C Q₁ R₁ Q₂ R₂ := by
  by_contra hnone
  push Not at hnone
  have hzero : (∑' m : d.graph.edgeFinset -> Nat,
      rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) = 0 := by
    rw [show (fun m : d.graph.edgeFinset -> Nat =>
        rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
          (fun _ => 0) by
      funext m
      exact not_ne_iff.mp (not_or.mp (hnone m)).1]
    exact tsum_zero
  exact hleft (left_reindex.trans hzero)





theorem actualMass_active_iff_pairReindex_defects_eq
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (transport : ∀ m hm T,
      (Q₁ (profileFlux d.graph m T) ∧
          R₁ (profileFlux d.graph m (univ \ T))) <->
        (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧
          R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
    (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) <->
      (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ -
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
      (shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss -
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
  let left := S.actualMass beta J d (s :: ss) *
    currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅
  let right := shb_segmentNum beta J d s *
    S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss
  let leftSum := ∑' m : d.graph.edgeFinset -> Nat,
    rawSourcePairFiberMass d.graph beta J m A Q₁ R₁
  let rightSum := ∑' m : d.graph.edgeFinset -> Nat,
    rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂
  have hsum : leftSum = rightSum := by
    apply tsum_congr
    exact pairMass_eq_of_contributingToggle d.graph beta J A C
      Q₁ R₁ Q₂ R₂ path path_sources transport
  change left = right <-> left - leftSum = right - rightSum
  constructor
  · intro hlr
    linarith
  · intro hdefect
    linarith

end BackbonePartialP2Reindex

end

end StatMech.Sharpness
