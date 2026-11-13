/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectSourceSeamBarrier
import Code.FrontierD.FKRectRankOneWindingTail
import Code.FrontierD.FKRectBoundaryVerticalFlux
import Code.FrontierD.FKRectAugmentedBarrierPatternCost



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def fkRectCutMedialColumn (R : FKRectTorus)
    (x : Fin R.width) (b : Bool) : Fin R.medialTorus.width :=
  (fkRectMedialVertexOfEdge R
    (b, (x, ⟨0, R.height_pos⟩))).1

@[simp] theorem fkRectCutMedialColumn_val
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    (fkRectCutMedialColumn R x b).val = b.toNat + 2 * x.val := by
  simp [fkRectCutMedialColumn]

@[simp] theorem fkRectCutMedialColumn_snd
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    (fkRectMedialVertexOfEdge R
      (b, (x, ⟨0, R.height_pos⟩))).2 = ⟨0, R.height_pos⟩ := by
  apply Fin.ext
  rfl

theorem fkRectCutMedialColumn_false_succ
    (R : FKRectTorus) (x : Fin R.width) :
    finitePeriodicSucc R.medialTorus.width_pos
        (fkRectCutMedialColumn R x false) =
      fkRectCutMedialColumn R x true := by
  apply Fin.ext
  rw [finitePeriodicSucc_val]
  have hne : 2 * x.val + 1 ≠ 2 * R.width := by omega
  simp [FKRectTorus.medialTorus, hne]
  omega

theorem fkRectTorusMedialEdgeEquiv_cutColumn
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      (b, (x, ⟨0, R.height_pos⟩)) := by
  rw [show (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      fkRectMedialVertexOfEdge R (b, (x, ⟨0, R.height_pos⟩)) by
    apply Prod.ext
    · rfl
    · apply Fin.ext; rfl]
  exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _



def fkRectCutMedialColumnEquiv (R : FKRectTorus) :
    Fin R.width × Bool ≃ Fin R.medialTorus.width where
  toFun xb := fkRectCutMedialColumn R xb.1 xb.2
  invFun i :=
    ((fkRectTorusMedialEdgeEquiv R (i, ⟨0, R.height_pos⟩)).2.1,
      (fkRectTorusMedialEdgeEquiv R (i, ⟨0, R.height_pos⟩)).1)
  left_inv := by
    rintro ⟨x, b⟩
    change ((fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩)).2.1,
      (fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩)).1) = (x, b)
    rw [show fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      (b, (x, ⟨0, R.height_pos⟩)) from
        fkRectTorusMedialEdgeEquiv_cutColumn R x b]
  right_inv := by
    intro i
    let e := fkRectTorusMedialEdgeEquiv R
      (i, ⟨0, R.height_pos⟩)
    have he : fkRectMedialVertexOfEdge R e =
        (i, ⟨0, R.height_pos⟩) := by
      exact (fkRectTorusMedialEdgeEquiv R).symm_apply_apply _
    change fkRectCutMedialColumn R e.2.1 e.1 = i
    unfold fkRectCutMedialColumn
    have hbase : e.2.2 = ⟨0, R.height_pos⟩ := by
      have hsnd := congrArg Prod.snd he
      exact hsnd
    rw [← hbase]
    exact congrArg Prod.fst he



theorem fkRectCutMedialColumn_canonicalVerticalSeamSign_add
    (R : FKRectTorus) (x : Fin R.width) :
    fkMedialCanonicalVerticalSeamSign R.medialTorus
        (fkRectCutMedialColumn R x false) +
      fkMedialCanonicalVerticalSeamSign R.medialTorus
        (fkRectCutMedialColumn R x true) = 0 := by
  unfold fkMedialCanonicalVerticalSeamSign fkMedialCheckerColor
    fkMedialVertexParity fkMedialVerticalSeamDart fkMedialSideVertical
  have heven : Even (2 * x.val) := even_two.mul_right x.val
  have hodd : ¬ Even (1 + 2 * x.val) := by
    rw [Nat.even_add]
    simp [heven]
  by_cases hrow : Even (svFinLast R.medialTorus.height_pos).val
  · simp [hrow, heven, hodd, fkRectCutMedialColumn_val]
  · simp [hrow, heven, hodd, fkRectCutMedialColumn_val]



theorem fkRectCutMedialColumns_reachable_of_both_open
    (R : FKRectTorus) (omega : R.Configuration) (x : Fin R.width)
    (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
    (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x false))
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x true)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let i0 := fkRectCutMedialColumn R x false
  let i1 := fkRectCutMedialColumn R x true
  let top0 := fkMedialVerticalSeamDart R.medialTorus i0
  let bot0 : FKMedialDart R.medialTorus :=
    ((i0, ⟨0, R.height_pos⟩), .south)
  let east0 : FKMedialDart R.medialTorus :=
    ((i0, ⟨0, R.height_pos⟩), .east)
  let west1 : FKMedialDart R.medialTorus :=
    ((i1, ⟨0, R.height_pos⟩), .west)
  let bot1 : FKMedialDart R.medialTorus :=
    ((i1, ⟨0, R.height_pos⟩), .south)
  let top1 := fkMedialVerticalSeamDart R.medialTorus i1
  have hi : finitePeriodicSucc R.medialTorus.width_pos i0 = i1 := by
    exact fkRectCutMedialColumn_false_succ R x
  have hv0 : fkRectTorusMedialEdgeEquiv R (i0, ⟨0, R.height_pos⟩) =
      (false, (x, ⟨0, R.height_pos⟩)) := by
    rw [show (i0, ⟨0, R.height_pos⟩) = fkRectMedialVertexOfEdge R
        (false, (x, ⟨0, R.height_pos⟩)) by
      apply Prod.ext
      · rfl
      · apply Fin.ext; rfl]
    exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _
  have hv1 : fkRectTorusMedialEdgeEquiv R (i1, ⟨0, R.height_pos⟩) =
      (true, (x, ⟨0, R.height_pos⟩)) := by
    rw [show (i1, ⟨0, R.height_pos⟩) = fkRectMedialVertexOfEdge R
        (true, (x, ⟨0, R.height_pos⟩)) by
      apply Prod.ext
      · rfl
      · apply Fin.ext; rfl]
    exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _
  have hp0 : pairing (i0, ⟨0, R.height_pos⟩) = false := by
    simp [pairing, fkRectConfigurationToMedialPairing_apply, hv0,
      hfalse, fkRectClosedPairingAtEdge]
  have hp1 : pairing (i1, ⟨0, R.height_pos⟩) = true := by
    simp [pairing, fkRectConfigurationToMedialPairing_apply, hv1,
      htrue, fkRectClosedPairingAtEdge]
  have h01 : (fkMedialLoopGraph R.medialTorus pairing).Adj top0 bot0 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [top0, bot0, fkMedialVerticalSeamDart, fkMedialBondMate,
      finitePeriodicSucc_svFinLast]
  have h12 : (fkMedialLoopGraph R.medialTorus pairing).Adj bot0 east0 := by
    rw [fkMedialLoopGraph_adj_iff]
    left
    simp [bot0, east0, fkMedialLocalMate, hp0]
  have h23 : (fkMedialLoopGraph R.medialTorus pairing).Adj east0 west1 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [east0, west1, fkMedialBondMate, hi]
  have h34 : (fkMedialLoopGraph R.medialTorus pairing).Adj west1 bot1 := by
    rw [fkMedialLoopGraph_adj_iff]
    left
    simp [west1, bot1, fkMedialLocalMate, hp1]
  have h45 : (fkMedialLoopGraph R.medialTorus pairing).Adj bot1 top1 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [top1, bot1, fkMedialVerticalSeamDart, fkMedialBondMate,
      SixVertexArrows.cyclicPred, svFinLast]
  exact h01.reachable.trans <| h12.reachable.trans <|
    h23.reachable.trans <| h34.reachable.trans h45.reachable



theorem fkRectCutMedialColumns_component_eq_of_both_open
    (R : FKRectTorus) (omega : R.Configuration) (x : Fin R.width)
    (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
    (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x false)) =
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x true)) := by
  exact ConnectedComponent.sound
    (fkRectCutMedialColumns_reachable_of_both_open
      R omega x hfalse htrue)



def fkRectMedialLoopCutColumnContribution
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (x : Fin R.width) (b : Bool) : Int := by
  classical
  exact if (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x b)) = C then
    fkMedialCanonicalVerticalSeamSign R.medialTorus
      (fkRectCutMedialColumn R x b)
  else 0


theorem fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C =
      ∑ x : Fin R.width,
        (fkRectMedialLoopCutColumnContribution R omega C x false +
          fkRectMedialLoopCutColumnContribution R omega C x true) := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
  calc
    (∑ i : Fin R.medialTorus.width,
      if (fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              (fkMedialVerticalSeamDart R.medialTorus i) = C then
        fkMedialCanonicalVerticalSeamSign R.medialTorus i else 0) =
      ∑ xb : Fin R.width × Bool,
        fkRectMedialLoopCutColumnContribution R omega C xb.1 xb.2 := by
      apply Fintype.sum_equiv (fkRectCutMedialColumnEquiv R).symm
      intro i
      unfold fkRectMedialLoopCutColumnContribution
      have hcol : fkRectCutMedialColumn R
          ((fkRectCutMedialColumnEquiv R).symm i).1
          ((fkRectCutMedialColumnEquiv R).symm i).2 = i := by
        simpa [fkRectCutMedialColumnEquiv] using
          (fkRectCutMedialColumnEquiv R).apply_symm_apply i
      rw [hcol]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_bool]
      ac_rfl



theorem fkRectAllButOneOpenSeamEvent_both_open_of_column_ne
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    {x : Fin R.width} (hx : x ≠ gap.2.1) :
    omega (false, (x, ⟨0, R.height_pos⟩)) = true ∧
      omega (true, (x, ⟨0, R.height_pos⟩)) = true := by
  have edge_ne (b : Bool) : (b, (x, ⟨0, R.height_pos⟩)) ≠ gap := by
    intro h
    apply hx
    exact congrArg (fun e : R.EdgeIndex => e.2.1) h
  constructor
  · exact (fkRectAllButOneOpenSeamEvent_open_iff R
      (homega := homega) (a := (false, (x, ⟨0, R.height_pos⟩)))
      (by simp [mem_fkRectHorizontalCutEdges_iff])).2 (edge_ne false)
  · exact (fkRectAllButOneOpenSeamEvent_open_iff R
      (homega := homega) (a := (true, (x, ⟨0, R.height_pos⟩)))
      (by simp [mem_fkRectHorizontalCutEdges_iff])).2 (edge_ne true)



theorem fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    {x : Fin R.width} (hx : x ≠ gap.2.1) :
    fkRectMedialLoopCutColumnContribution R omega C x false +
      fkRectMedialLoopCutColumnContribution R omega C x true = 0 := by
  classical
  obtain ⟨hfalse, htrue⟩ :=
    fkRectAllButOneOpenSeamEvent_both_open_of_column_ne
      R homega hx
  have hcomponent := fkRectCutMedialColumns_component_eq_of_both_open
    R omega x hfalse htrue
  unfold fkRectMedialLoopCutColumnContribution
  by_cases hC :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x false)) = C
  · rw [if_pos hC, if_pos (hcomponent ▸ hC)]
    exact fkRectCutMedialColumn_canonicalVerticalSeamSign_add R x
  · have hC' :
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkMedialVerticalSeamDart R.medialTorus
              (fkRectCutMedialColumn R x true)) ≠ C := by
      rwa [← hcomponent]
    simp [hC, hC']



theorem fkMedialLoopCanonicalVerticalFlux_eq_gapColumn
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C =
      fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false +
        fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true := by
  rw [fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns]
  classical
  rw [Finset.sum_eq_single gap.2.1]
  · intro x hx hne
    exact fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap
      R homega C hne
  · simp



theorem sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one
    (R : FKRectTorus) (omega : R.Configuration)
    (x : Fin R.width) (b : Bool) :
    ∑ C : FKMedialLoop R.medialTorus
        (fkRectConfigurationToMedialPairing R omega),
      (fkRectMedialLoopCutColumnContribution R omega C x b).natAbs = 1 := by
  classical
  let C0 := (fkMedialLoopGraph R.medialTorus
    (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
      (fkMedialVerticalSeamDart R.medialTorus
        (fkRectCutMedialColumn R x b))
  rw [Finset.sum_eq_single C0]
  · unfold fkRectMedialLoopCutColumnContribution
    rw [if_pos rfl]
    unfold fkMedialCanonicalVerticalSeamSign
    split <;> simp
  · intro C hC hne
    unfold fkRectMedialLoopCutColumnContribution
    rw [if_neg]
    · rfl
    · exact hne.symm
  · simp



theorem fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    fkMedialUnorientedVerticalWindingTotal
        (fkRectConfigurationToMedialPairing R omega) ≤ 2 := by
  classical
  unfold fkMedialUnorientedVerticalWindingTotal
  calc
    (∑ C : FKMedialLoop R.medialTorus
        (fkRectConfigurationToMedialPairing R omega),
      (fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C).natAbs) =
      ∑ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false +
          fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true).natAbs := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [fkMedialLoopCanonicalVerticalFlux_eq_gapColumn
        R homega C]
    _ ≤ ∑ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        ((fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false).natAbs +
          (fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true).natAbs) := by
      apply Finset.sum_le_sum
      intro C hC
      exact Int.natAbs_add_le _ _
    _ = 2 := by
      rw [Finset.sum_add_distrib,
        sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one,
        sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one]


theorem fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    fkRectUnorientedVerticalWindingNumber R omega ≤ 1 := by
  unfold fkRectUnorientedVerticalWindingNumber
    fkRectUnorientedVerticalWindingTotal
  have h :=
    fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam
      R homega
  omega



theorem fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex)
    (x : Fin R.width) :
    fkRectAugmentedSourceBarrier R leftRight gap x ⊆
      fkRectAllButOneOpenSeamEvent R gap := by
  intro omega homega a ha
  exact homega.2 a (Finset.mem_union_left _ ha)



theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne
    (R : FKRectTorus) (leftRight cut : Nat)
    (hleft : leftRight + 1 < R.width)
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
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hseparated : omega ∈
      fkRectSeparatedVerticalWindingEvent R leftRight :=
    fkRectFullGraphEvent_to_indexed R _
      (fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
        R leftRight cut hgap x hx hchosen t hpair hrho)
  have hrank : omega ∈ fkRectVerticalRankOneEvent R :=
    fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne
      R leftRight hleft hseparated
  have hlower : 1 ≤ fkRectUnorientedVerticalWindingNumber R omega :=
    fkRectVerticalRankOneEvent_subset_windingTail R hrank
  have hupper : fkRectUnorientedVerticalWindingNumber R omega ≤ 1 :=
    fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
      R (fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent
        R leftRight gap x hbarrier)
  exact le_antisymm hupper hlower



theorem fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
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
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have htarget :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne
        R leftRight cut hleft hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}
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



theorem fkRectSource_barrierConnectionProduct_le_windingOneMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    FK.cFE (fkRectCriticalP q) q *
        (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  let P : Real := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro xy hxy
    exact FK.twoPointFun_nonneg
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq))
      (zero_lt_one.trans_le hq) xy.1 xy.2
  calc
    FK.cFE (fkRectCriticalP q) q * P *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) =
      P * (FK.cFE (fkRectCriticalP q) q *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap)) := by ring
    _ ≤ P * fkRectCriticalEventMass R q
        (fkRectAugmentedSourceBarrier R leftRight gap x) :=
      mul_le_mul_of_nonneg_left
        (fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier
          R leftRight gap x (by omega) hq) hP
    _ ≤ fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} :=
      fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass
        R leftRight cut hsep hleft hq hgap x hx hchosen t hpair

end

end StatMech.FrontierD
