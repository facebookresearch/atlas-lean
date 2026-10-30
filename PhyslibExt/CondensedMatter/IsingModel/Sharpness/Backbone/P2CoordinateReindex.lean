/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialP2Reindex

/-!
# Coordinate reindexing of the P2 cut resummation identity

Currents on a subgraph extend by zero to currents on the ambient graph with the same sources and
weight. Using this, both sides of the active cut resummation identity for a partial current
dynamic selector are written as sums of raw pair fiber masses on the domain graph, and the identity
follows from a contributing-path toggle with a transport condition.

## i. Overview

For `H ≤ G`, `extendFlux` extends an edge function on `H` by zero; it is injective and preserves
sources and weights. Lifting predicates through it, sums over currents of `H` become sums over
currents of `G` (`tsum_liftedPredicate_eq`); in particular the sourceless partition function of the
residual graph after exploring a segment is a lifted sum on the domain graph.

The two sides of the active identity `fiber(s :: ss) × Z(residual) = N(s) × fiber(ss)` are then
sums over fluxes `m` of raw pair fiber masses with sources `sourceClass(s :: ss)` and
`{s.1, s.2.1}` (`partialActualMass_mul_residualCurrentSum_eq_pairTsum`,
`segmentNum_mul_partialActualMass_eq_pairTsum`), and the labeled edge-copy toggle of
`PartialP2Reindex` matches them given a contributing-path selector with the right sources and a
transport equivalence (`actualMass_active_of_coordinateToggle`).

Headline fidelity:
- The extension lemmas, `tsum_liftedPredicate_eq`, `tsum_liftedVacuum_eq_currentSum`,
  `partialActualMass_mul_residualCurrentSum_eq_pairTsum` and
  `segmentNum_mul_partialActualMass_eq_pairTsum` are unconditional.
- `actualMass_active_of_coordinateToggle` is conditional on a contributing-path selector `path`,
  its source condition `path_sources` and the transport equivalence `transport`. These data do not
  exist for the vacuum selector when the segment numerator is nonzero
  (`vacuumCoordinateToggleData_isEmpty`, `P2CoordinateToggleObstruction`); they are not
  constructed here for any selector, and the identity is a form of the backbone chain rule (P2).

## ii. Key results

- `extendFlux` : extension by zero of currents on a subgraph
- `tsum_liftedPredicate_eq` : sums over subgraph currents as lifted sums (unconditional)
- `partialActualMass_mul_residualCurrentSum_eq_pairTsum`,
  `segmentNum_mul_partialActualMass_eq_pairTsum` : both sides as pair fiber mass sums
  (unconditional)
- `actualMass_active_of_coordinateToggle` : the active cut resummation identity (conditional on
  `path`, `path_sources`, `transport`)

## iii. Table of contents

- A. Extension by zero from a subgraph
- B. Lifted predicates
- C. Both sides as pair fiber masses
- D. The coordinate toggle

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
noncomputable local instance coordinateReindexDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

namespace BackboneP2CoordinateReindex

open BackboneLabeledSwitching
open BackbonePartialP2Reindex

variable {H G : SimpleGraph V}

/-! ## A. Extension by zero from a subgraph -/

/-- The extension by zero of an edge function on `H ≤ G` to an edge function on `G`. -/
noncomputable def extendFlux (_hHG : H ≤ G)
    (r : H.edgeFinset -> Nat) : G.edgeFinset -> Nat := fun e =>
  if he : e.1 ∈ H.edgeFinset then r ⟨e.1, he⟩ else 0

omit [DecidableEq V] in
/-- The edges of a subgraph are edges of the ambient graph. -/
lemma edgeFinset_subset (hHG : H ≤ G) : H.edgeFinset ⊆ G.edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  exact edgeSet_mono hHG he

lemma extendFlux_injective (hHG : H ≤ G) :
    Function.Injective (extendFlux hHG) := by
  intro r t hrt
  funext e
  have heG : e.1 ∈ G.edgeFinset := edgeFinset_subset hHG e.2
  have heq := congrFun hrt (⟨e.1, heG⟩ : G.edgeFinset)
  simpa [extendFlux, e.2] using heq

lemma ofEdgeFun_extendFlux (hHG : H ≤ G) (r : H.edgeFinset -> Nat) :
    ofEdgeFun G (extendFlux hHG r) = ofEdgeFun H r := by
  funext e
  by_cases heH : e ∈ H.edgeFinset
  · have heG : e ∈ G.edgeFinset := edgeFinset_subset hHG heH
    simp [ofEdgeFun, extendFlux, heH, heG]
  · simp [ofEdgeFun, extendFlux, heH]

lemma incidentFlux_extendFlux (hHG : H ≤ G)
    (r : H.edgeFinset -> Nat) (x : V) :
    incidentFlux G (ofEdgeFun G (extendFlux hHG r)) x =
      incidentFlux H (ofEdgeFun H r) x := by
  rw [ofEdgeFun_extendFlux hHG r]
  unfold incidentFlux
  symm
  apply Finset.sum_subset
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨edgeFinset_subset hHG he.1, he.2⟩
  · intro e heG heH
    rw [Finset.mem_filter] at heG
    have hnot : e ∉ H.edgeFinset := by
      intro he
      exact heH (by simp [he, heG.2])
    simp [ofEdgeFun, hnot]

/-- Extension by zero preserves sources. -/
lemma sources_extendFlux (hHG : H ≤ G) (r : H.edgeFinset -> Nat) :
    sources G (ofEdgeFun G (extendFlux hHG r)) =
      sources H (ofEdgeFun H r) := by
  ext x
  simp only [mem_sources]
  rw [incidentFlux_extendFlux hHG r x]

/-- Extension by zero preserves weights. -/
lemma weight_extendFlux (hHG : H ≤ G) (beta : Real)
    (J : Sym2 V -> Real) (r : H.edgeFinset -> Nat) :
    weight G beta J (ofEdgeFun G (extendFlux hHG r)) =
      weight H beta J (ofEdgeFun H r) := by
  rw [ofEdgeFun_extendFlux hHG r]
  unfold weight
  symm
  apply Finset.prod_subset (edgeFinset_subset hHG)
  intro e heG heH
  have hzero : ofEdgeFun H r e = 0 := by
    simp [ofEdgeFun, heH]
  simp [hzero]

/-! ## B. Lifted predicates -/

/-- A predicate on currents of `H` lifted to currents of `G`: the current is the extension of a
current of `H` satisfying the predicate. -/
def LiftedPredicate (hHG : H ≤ G)
    (P : (H.edgeFinset -> Nat) -> Prop)
    (q : G.edgeFinset -> Nat) : Prop :=
  ∃ r, extendFlux hHG r = q ∧ P r

/-- Classical decidability of lifted predicates. -/
noncomputable instance liftedPredicateDecidable (hHG : H ≤ G)
    (P : (H.edgeFinset -> Nat) -> Prop) :
    DecidablePred (LiftedPredicate hHG P) := Classical.decPred _

lemma liftedPredicate_witness_unique (hHG : H ≤ G)
    {q : G.edgeFinset -> Nat}
    {r t : H.edgeFinset -> Nat}
    (hr : extendFlux hHG r = q) (ht : extendFlux hHG t = q) : r = t :=
  extendFlux_injective hHG (hr.trans ht.symm)

/-- The weight mass of a lifted predicate on `G` is the weight mass of the predicate on `H`. -/
lemma tsum_liftedPredicate_eq
    (hHG : H ≤ G) (beta : Real) (J : Sym2 V -> Real)
    (P : (H.edgeFinset -> Nat) -> Prop) [DecidablePred P] :
    (∑' q : G.edgeFinset -> Nat,
        if LiftedPredicate hHG P q then
          weight G beta J (ofEdgeFun G q) else 0) =
      ∑' r : H.edgeFinset -> Nat,
        if P r then weight H beta J (ofEdgeFun H r) else 0 := by
  classical
  let e : (H.edgeFinset -> Nat) ≃ Set.range (extendFlux hHG) :=
    Equiv.ofInjective (extendFlux hHG) (extendFlux_injective hHG)
  calc
    (∑' q : G.edgeFinset -> Nat,
        if LiftedPredicate hHG P q then
          weight G beta J (ofEdgeFun G q) else 0) =
        ∑' q : Set.range (extendFlux hHG),
          if LiftedPredicate hHG P q.1 then
            weight G beta J (ofEdgeFun G q.1) else 0 := by
      have hsub := _root_.tsum_subtype (Set.range (extendFlux hHG))
        (fun q => if LiftedPredicate hHG P q then
          weight G beta J (ofEdgeFun G q) else 0)
      refine (tsum_congr fun q => ?_).trans hsub.symm
      by_cases hq : q ∈ Set.range (extendFlux hHG)
      · simp [Set.indicator, hq]
      · have hlift : ¬LiftedPredicate hHG P q := by
          rintro ⟨r, hr, _⟩
          exact hq ⟨r, hr⟩
        simp [Set.indicator, hq, hlift]
    _ = ∑' r : H.edgeFinset -> Nat,
          if P r then
            weight G beta J (ofEdgeFun G (extendFlux hHG r)) else 0 := by
      rw [← e.tsum_eq]
      apply tsum_congr
      intro r
      have hiff : LiftedPredicate hHG P (extendFlux hHG r) <-> P r := by
        constructor
        · rintro ⟨t, ht, hPt⟩
          have htr : t = r := extendFlux_injective hHG ht
          simpa [htr] using hPt
        · intro hPr
          exact ⟨r, rfl, hPr⟩
      simp [e, hiff]
    _ = ∑' r : H.edgeFinset -> Nat,
          if P r then weight H beta J (ofEdgeFun H r) else 0 := by
      apply tsum_congr
      intro r
      by_cases hP : P r <;> simp [hP, weight_extendFlux hHG beta J r]

/-- The lifted weight mass of the sourceless currents of `H` is the sourceless partition function
of `H`. -/
lemma tsum_liftedVacuum_eq_currentSum
    (hHG : H ≤ G) (beta : Real) (J : Sym2 V -> Real) :
    (∑' q : G.edgeFinset -> Nat,
        if LiftedPredicate hHG
            (fun r => sources H (ofEdgeFun H r) = ∅) q then
          weight G beta J (ofEdgeFun G q) else 0) =
      currentSum H beta J ∅ := by
  rw [tsum_liftedPredicate_eq hHG beta J]
  rfl

/-! ## C. Both sides as pair fiber masses -/

lemma rawPairFiberMass_eq_rawSourcePairFiberMass
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat)
    (R : (d.graph.edgeFinset -> Nat) -> Prop) [DecidablePred R] :
    rawPairFiberMass d.graph beta J m (S.Fiber d word) R =
      rawSourcePairFiberMass d.graph beta J m
        (S.sourceClass d word) (S.Fiber d word) R := by
  classical
  unfold rawSourcePairFiberMass rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  by_cases hF : S.Fiber d word K.1
  · have hsrc : sources d.graph (ofEdgeFun d.graph K.1) =
        S.sourceClass d word :=
      S.sources_eq_sourceClass_of_select d K.1 word hF
    simp [hF, hsrc]
  · simp [hF]

/-- The left side `fiber(s :: ss) × Z(residual)` as a sum of raw pair fiber masses. -/
lemma partialActualMass_mul_residualCurrentSum_eq_pairTsum
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawSourcePairFiberMass d.graph beta J m
          (S.sourceClass d (s :: ss)) (S.Fiber d (s :: ss))
          (LiftedPredicate
            (d.graph.deleteEdges_le s.edgeSet)
            (fun r => sources
              (shb_BackboneExplorationDomain.advance d s).graph
              (ofEdgeFun
                (shb_BackboneExplorationDomain.advance d s).graph r) = ∅)) := by
  let H := (shb_BackboneExplorationDomain.advance d s).graph
  let hHG : H ≤ d.graph := d.graph.deleteEdges_le s.edgeSet
  rw [show S.actualMass beta J d (s :: ss) =
      ∑' p : d.graph.edgeFinset -> Nat,
        if S.Fiber d (s :: ss) p then
          weight d.graph beta J (ofEdgeFun d.graph p) else 0 by rfl]
  rw [show currentSum H beta J ∅ =
      ∑' q : d.graph.edgeFinset -> Nat,
        if LiftedPredicate hHG
            (fun r => sources H (ofEdgeFun H r) = ∅) q then
          weight d.graph beta J (ofEdgeFun d.graph q) else 0 by
    exact (tsum_liftedVacuum_eq_currentSum hHG beta J).symm]
  rw [rawPairFiberMass_tsum_eq_mul]
  apply tsum_congr
  intro m
  exact rawPairFiberMass_eq_rawSourcePairFiberMass S beta J d
    (s :: ss) m _

lemma segmentNum_eq_fiberTsum
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) :
    shb_segmentNum beta J d s =
      ∑' p : d.graph.edgeFinset -> Nat,
        if shb_ActiveSegmentFiber d s hs p then
          weight d.graph beta J (ofEdgeFun d.graph p) else 0 := by
  exact (shb_activeSegmentFiberMass_eq_segmentNum beta J d s hs).symm

lemma rawPairFiberMass_eq_rawActivePairFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat)
    (R : (d.graph.edgeFinset -> Nat) -> Prop) [DecidablePred R] :
    rawPairFiberMass d.graph beta J m
        (shb_ActiveSegmentFiber d s hs) R =
      rawSourcePairFiberMass d.graph beta J m {s.1, s.2.1}
        (shb_ActiveSegmentFiber d s hs) R := by
  classical
  unfold rawSourcePairFiberMass rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  by_cases hF : shb_ActiveSegmentFiber d s hs K.1
  · have hsrc := hF.1
    simp [hF, hsrc]
  · simp [hF]

open Classical in
/-- The right side `N(s) × fiber(ss)` as a sum of raw pair fiber masses. -/
lemma segmentNum_mul_partialActualMass_eq_pairTsum
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawSourcePairFiberMass d.graph beta J m {s.1, s.2.1}
          (shb_ActiveSegmentFiber d s hs)
          (LiftedPredicate
            (d.graph.deleteEdges_le s.edgeSet)
            (S.Fiber (shb_BackboneExplorationDomain.advance d s) ss)) := by
  let H := (shb_BackboneExplorationDomain.advance d s).graph
  let hHG : H ≤ d.graph := d.graph.deleteEdges_le s.edgeSet
  rw [segmentNum_eq_fiberTsum beta J d s hs]
  rw [show S.actualMass beta J
      (shb_BackboneExplorationDomain.advance d s) ss =
      ∑' q : d.graph.edgeFinset -> Nat,
        if LiftedPredicate hHG
            (S.Fiber (shb_BackboneExplorationDomain.advance d s) ss) q then
          weight d.graph beta J (ofEdgeFun d.graph q) else 0 by
    exact (tsum_liftedPredicate_eq hHG beta J
      (S.Fiber (shb_BackboneExplorationDomain.advance d s) ss)).symm]
  rw [rawPairFiberMass_tsum_eq_mul]
  apply tsum_congr
  intro m
  exact rawPairFiberMass_eq_rawActivePairFiberMass beta J d s hs m _

/-! ## D. The coordinate toggle -/

/-- The sources to toggle: `sourceClass(s :: ss) ∆ {s.1, s.2.1}`. -/
def stepToggleSource
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) : Finset V :=
  S.sourceClass d (s :: ss) ∆ {s.1, s.2.1}

/-- The lifted sourceless-current predicate of the residual graph. -/
def liftedResidualVacuum
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    (d.graph.edgeFinset -> Nat) -> Prop :=
  LiftedPredicate (d.graph.deleteEdges_le s.edgeSet)
    (fun r => sources (shb_BackboneExplorationDomain.advance d s).graph
      (ofEdgeFun (shb_BackboneExplorationDomain.advance d s).graph r) = ∅)

/-- The lifted fiber of `ss` in the residual domain. -/
def liftedResidualFiber
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    (d.graph.edgeFinset -> Nat) -> Prop :=
  LiftedPredicate (d.graph.deleteEdges_le s.edgeSet)
    (S.Fiber (shb_BackboneExplorationDomain.advance d s) ss)

/-- Classical decidability of the lifted residual vacuum predicate. -/
noncomputable instance liftedResidualVacuumDecidable
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    DecidablePred (liftedResidualVacuum d s) := Classical.decPred _

/-- Classical decidability of the lifted residual fiber. -/
noncomputable instance liftedResidualFiberDecidable
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    DecidablePred (liftedResidualFiber S d s ss) := Classical.decPred _

/-- The active cut resummation identity for a partial selector, given a contributing-path
selector with sources `stepToggleSource` and a transport equivalence between the two pair fibers. -/
lemma actualMass_active_of_coordinateToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
      (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss))
    (path_sources : ∀ m hm,
      RandomCurrent.sources (FluxEdgeCopy.endsM d.graph m) (path m hm) =
        stepToggleSource S d s ss)
    (transport : ∀ m hm T,
      (S.Fiber d (s :: ss) (FluxEdgeCopy.profileFlux d.graph m T) ∧
          liftedResidualVacuum d s
            (FluxEdgeCopy.profileFlux d.graph m (univ \ T))) <->
        (shb_ActiveSegmentFiber d s hs
            (FluxEdgeCopy.profileFlux d.graph m (T ∆ path m hm)) ∧
          liftedResidualFiber S d s ss
            (FluxEdgeCopy.profileFlux d.graph m
              (univ \ (T ∆ path m hm))))) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  apply actualMass_active_of_contributingToggle S beta J d s ss
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
    ?_ ?_ path path_sources transport
  · exact partialActualMass_mul_residualCurrentSum_eq_pairTsum
      S beta J d s ss
  · have h := segmentNum_mul_partialActualMass_eq_pairTsum S beta J d s ss hs
    try simp only [stepToggleSource]
    rw [symmDiff_symmDiff_cancel_left]
    exact h

end BackboneP2CoordinateReindex

end

end StatMech.Sharpness
