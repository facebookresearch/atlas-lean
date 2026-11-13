/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectAugmentedSourceBarrier



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def fkRectIndexedConfigurationOfFullGraph (R : FKRectTorus)
    (rho : ConfigSpace (Sym2 R.Vertex)) : R.Configuration :=
  (fkRectFullEdgeConfigEquiv R).symm
    (FK.ecz_closeOff (fkRectTorusGraph R) rho)

theorem fkRectFullGraphEvent_to_indexed
    (R : FKRectTorus) (B : Set R.Configuration)
    {rho : ConfigSpace (Sym2 R.Vertex)}
    (hrho : rho ∈ fkRectFullGraphEvent R B) :
    fkRectIndexedConfigurationOfFullGraph R rho ∈ B :=
  hrho



theorem fkRectInduced_openSub_indexedConfiguration_eq
    (R : FKRectTorus) (S : Set R.Vertex)
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)
          (fkRectFullGraphConfiguration R
            (fkRectIndexedConfigurationOfFullGraph R rho))) =
      FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho) := by
  let sigma := FK.ecz_closeOff (fkRectTorusGraph R) rho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hsigma : fkRectFullEdgeConfigEquiv R omega = sigma := by
    exact (fkRectFullEdgeConfigEquiv R).apply_symm_apply sigma
  have hfull : fkRectFullGraphConfiguration R omega = sigma.1 :=
    congrArg Subtype.val hsigma
  ext u v
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have hedge : s(u.1, v.1) ∈ (fkRectTorusGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    change fkRectFullGraphConfiguration R omega s(u.1, v.1) = true at hopen
    change rho s(u.1, v.1) = true
    rw [hfull, FK.ecz_closeOff_apply_edge _ _ hedge] at hopen
    exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have hedge : s(u.1, v.1) ∈ (fkRectTorusGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    change rho s(u.1, v.1) = true at hopen
    change fkRectFullGraphConfiguration R omega s(u.1, v.1) = true
    rw [hfull, FK.ecz_closeOff_apply_edge _ _ hedge]
    exact hopen

theorem fkRectInduced_connectionChain_to_indexedConfiguration
    (R : FKRectTorus) (S : Set R.Vertex)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S))
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho ∈
        fkRectInducedConnectionChainEvent R S t) :
    FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S → R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectIndexedConfigurationOfFullGraph R rho)) ∈
      fkRectInducedConnectionChainEvent R S t := by
  intro p hp
  have hreach := hchain p hp
  change (FK.openSub (fkRectInducedGraph R S)
    (FK.ocd_innerRestrict
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)
      (fkRectFullGraphConfiguration R
        (fkRectIndexedConfigurationOfFullGraph R rho)))).Reachable p.1 p.2
  change (FK.openSub (fkRectInducedGraph R S)
    (FK.ocd_innerRestrict
      (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho)).Reachable
        p.1 p.2 at hreach
  rw [fkRectInduced_openSub_indexedConfiguration_eq R S rho]
  exact hreach



theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
    (R : FKRectTorus) (leftRight cut : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    fkRectAugmentedBarrierConnectionEvent R
        leftRight cut gap x t ⊆
      fkRectFullGraphEvent R (fkRectVerticalWindingEvent R) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t := by
    exact fkRectInduced_connectionChain_to_indexedConfiguration R
      (fkRectRightStripBand R cut 1 (R.height - 1)) rho t hrho.1
  have hopen := fkRectAugmentedSourceBarrier_witnessEdges_open
    R leftRight hgap x hchosen hbarrier
  change omega ∈ fkRectVerticalWindingEvent R
  exact fkRectVerticalWindingEvent_of_rightBand_chain
    R cut x hx omega t hpair hchain hopen.1 hopen.2




def fkRectSeparatedVerticalWindingEvent (R : FKRectTorus)
    (leftRight : Nat) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectVerticalWindingEvent R

theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
    (R : FKRectTorus) (leftRight cut : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    fkRectAugmentedBarrierConnectionEvent R
        leftRight cut gap x t ⊆
      fkRectFullGraphEvent R
        (fkRectSeparatedVerticalWindingEvent R leftRight) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hwinding :=
    fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
      R leftRight cut hgap x hx hchosen t hpair hrho
  exact ⟨hbarrier.1, hwinding⟩



theorem fkRectAugmentedSource_barrierConnectionProduct_le_verticalWindingMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    (fkRectVerticalWindingEvent R)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have hwinding :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
        R leftRight cut hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem hwinding]
  · by_cases hwinding : rho ∈
        fkRectFullGraphEvent R (fkRectVerticalWindingEvent R)
    · rw [Set.indicator_of_notMem hsource,
        Set.indicator_of_mem hwinding]
      have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
      simpa using
        (FK.fkProb_nonneg (G := fkRectTorusGraph R)
          (p := fkRectCriticalP q) (q := q)
          (fkRectCriticalP_pos hq0)
          (fkRectCriticalP_lt_one hq0) hq0 rho)
    · simp [Set.indicator_of_notMem hsource,
        Set.indicator_of_notMem hwinding]


theorem fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalEventMass R q
        (fkRectSeparatedVerticalWindingEvent R leftRight) := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    (fkRectSeparatedVerticalWindingEvent R leftRight)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have htarget :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
        R leftRight cut hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        (fkRectSeparatedVerticalWindingEvent R leftRight)
    · rw [Set.indicator_of_notMem hsource,
        Set.indicator_of_mem htarget]
      have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
      simpa using
        (FK.fkProb_nonneg (G := fkRectTorusGraph R)
          (p := fkRectCriticalP q) (q := q)
          (fkRectCriticalP_pos hq0)
          (fkRectCriticalP_lt_one hq0) hq0 rho)
    · simp [Set.indicator_of_notMem hsource,
        Set.indicator_of_notMem htarget]

end

end StatMech.FrontierD
