/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopLexUnitFineRelation











open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexFullComponentMaskSwapPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



def SixVertexFullDisagreementMask
    {T : EvenTorus} (omega eta mask : SixVertexArrows T) : Prop :=
  (forall v d, sixVertexTorusLocalSwitchMask mask v d = true ->
    sixVertexLocalIncomingPattern omega v d ≠
      sixVertexLocalIncomingPattern eta v d) /\
  (forall v d r, sixVertexTorusLocalSwitchMask mask v d = true ->
    sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r ->
    sixVertexTorusLocalSwitchMask mask v r = true)

theorem SixVertexFullDisagreementMask.local_eq_disagreement
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex)
    (hactive : exists d,
      sixVertexTorusLocalSwitchMask mask v d = true) :
    forall r, sixVertexTorusLocalSwitchMask mask v r =
      decide (sixVertexLocalIncomingPattern omega v r ≠
        sixVertexLocalIncomingPattern eta v r) := by
  obtain ⟨d, hd⟩ := hactive
  intro r
  by_cases hr : sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r
  · rw [hmask.2 v d r hd hr]
    simp [hr]
  · have hfalse : sixVertexTorusLocalSwitchMask mask v r = false := by
      cases hm : sixVertexTorusLocalSwitchMask mask v r
      · rfl
      · exact False.elim (hr (hmask.1 v r hm))
    rw [hfalse]
    simp [hr]

theorem SixVertexFullDisagreementMask.local_eq_or_swap
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex) :
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
        (sixVertexLocalIncomingPattern omega v,
          sixVertexLocalIncomingPattern eta v) \/
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
        (sixVertexLocalIncomingPattern eta v,
          sixVertexLocalIncomingPattern omega v) := by
  rw [sixVertexTorusLocalIncomingPattern_pairSwitch]
  by_cases hactive : exists d,
      sixVertexTorusLocalSwitchMask mask v d = true
  · right
    exact sixVertexLocalSwapMask_eq_pair_of_disagreementMask _ _ _
      (hmask.local_eq_disagreement v hactive)
  · left
    have hzero : sixVertexTorusLocalSwitchMask mask v = fun _ => false := by
      funext d
      cases hm : sixVertexTorusLocalSwitchMask mask v d
      · rfl
      · exact False.elim (hactive ⟨d, hm⟩)
    simp [sixVertexLocalSwapMask, hzero]

theorem SixVertexFullDisagreementMask.localCTypeCount
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex) :
    sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v)
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v) =
      sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) := by
  rcases hmask.local_eq_or_swap v with hsame | hswap
  · rw [show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v =
        sixVertexLocalIncomingPattern omega v by
          exact congrArg Prod.fst hsame,
      show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v =
        sixVertexLocalIncomingPattern eta v by
          exact congrArg Prod.snd hsame]
  · rw [show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v =
        sixVertexLocalIncomingPattern eta v by
          exact congrArg Prod.fst hswap,
      show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v =
        sixVertexLocalIncomingPattern omega v by
          exact congrArg Prod.snd hswap]
    simp only [sixVertexLocalCTypeCount, add_comm]

theorem SixVertexFullDisagreementMask.boundedFineRowProfile
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (omega.horizontal, eta.horizontal) := by
  apply sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
  funext j
  apply Prod.ext
  · change sixVertexHorizontalPairRowNontransitionProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) j =
      sixVertexHorizontalPairRowNontransitionProfile
        (omega.horizontal, eta.horizontal) j
    unfold
      sixVertexHorizontalPairRowNontransitionProfile
    rw [sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      <- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [sixVertexLocalCTypeCount,
      sixVertexLocalIncomingPattern_isCType_iff] using
        hmask.localCTypeCount (i, j)
  · change sixVertexHorizontalPairRowZeroProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) j =
      sixVertexHorizontalPairRowZeroProfile
        (omega.horizontal, eta.horizontal) j
    exact congrFun
      (sixVertexTorusPairSwitch_rowZeroProfile mask omega eta) j


noncomputable def sixVertexSeedDisagreementComponentMask
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed : SixVertexTorusEdge T) : SixVertexArrows T := by
  classical
  let G := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (G.Reachable seed (0, v))
      vertical := fun v => decide (G.Reachable seed (1, v)) }

theorem sixVertexSeedDisagreementComponentMask_selects_iff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed e : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexSeedDisagreementComponentMask omega eta seed) e = true <->
      (sixVertexTorusDisagreementGraph omega eta).Reachable seed e := by
  classical
  rcases e with ⟨dir, v⟩
  fin_cases dir <;>
    simp [sixVertexTorusMaskSelects,
      sixVertexSeedDisagreementComponentMask]

theorem sixVertexSeedDisagreementComponentMask_full
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed : SixVertexTorusEdge T)
    (hseed : sixVertexTorusEdgeDisagrees omega eta seed) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexSeedDisagreementComponentMask omega eta seed) := by
  let mask := sixVertexSeedDisagreementComponentMask omega eta seed
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexDisagreementGraph_reachable_disagrees hseed
    rw [sixVertexTorusLocalSwitchMask_apply] at hd
    exact (sixVertexSeedDisagreementComponentMask_selects_iff
      omega eta seed _).1 hd
  · intro v d r hd hr
    rw [sixVertexTorusLocalSwitchMask_apply] at hd ⊢
    rw [sixVertexSeedDisagreementComponentMask_selects_iff] at hd ⊢
    by_cases hdr : sixVertexTorusIncidentEdge T v d =
        sixVertexTorusIncidentEdge T v r
    · simpa [hdr] using hd
    · apply hd.trans
      apply SimpleGraph.Adj.reachable
      refine ⟨hdr, ?_, ?_, v, d, r, rfl, rfl⟩
      · exact sixVertexDisagreementGraph_reachable_disagrees hseed hd
      · exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
          omega eta v r).1 hr

def sixVertexFullDisagreementVertexMask
    {T : EvenTorus} (mask : SixVertexArrows T) : T.Vertex -> Bool :=
  sixVertexTorusEdgeMaskVertexMask mask

theorem SixVertexFullDisagreementMask.vertexMask_bondMate
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexFullDisagreementVertexMask mask d.1 =
      sixVertexFullDisagreementVertexMask mask
        (sixVertexTorusDartBondMate T d).1 := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  have hlocal : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hforward (hactive : vertexMask d.1 = true) :
      vertexMask (sixVertexTorusDartBondMate T d).1 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).1 hactive
    have hd := hmask.2 d.1 side d.2 hside hlocal
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask _).2
    exact ⟨(sixVertexTorusDartBondMate T d).2, by
      rw [sixVertexTorusLocalSwitchMask_bondMate mask d]
      exact hd⟩
  have hreverse
      (hactive : vertexMask (sixVertexTorusDartBondMate T d).1 = true) :
      vertexMask d.1 = true := by
    let mate := sixVertexTorusDartBondMate T d
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask mate.1).1 hactive
    have hlocalMate : sixVertexLocalIncomingPattern omega mate.1 mate.2 ≠
        sixVertexLocalIncomingPattern eta mate.1 mate.2 := by
      rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      change sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusDartEdge T (sixVertexTorusDartBondMate T d))
      rw [sixVertexTorusDartEdge_bondMate]
      exact hdisagrees
    have hm := hmask.2 mate.1 side mate.2 hside hlocalMate
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).2
    exact ⟨d.2, by
      rw [← sixVertexTorusLocalSwitchMask_bondMate mask d]
      exact hm⟩
  change vertexMask d.1 =
    vertexMask (sixVertexTorusDartBondMate T d).1
  cases hfirst : vertexMask d.1 <;>
    cases hsecond : vertexMask (sixVertexTorusDartBondMate T d).1
  · rfl
  · exact False.elim (by simpa [hfirst] using hreverse hsecond)
  · exact False.elim (by simpa [hsecond] using hforward hfirst)
  · rfl

theorem SixVertexFullDisagreementMask.vertexMask_eq_localMask_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexFullDisagreementVertexMask mask d.1 =
      sixVertexTorusLocalSwitchMask mask d.1 d.2 := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  have hlocal : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hselectedToActive
      (hselected : sixVertexTorusLocalSwitchMask mask d.1 d.2 = true) :
      vertexMask d.1 = true :=
    (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).2
      ⟨d.2, hselected⟩
  have hactiveToSelected (hactive : vertexMask d.1 = true) :
      sixVertexTorusLocalSwitchMask mask d.1 d.2 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff mask d.1).1 hactive
    exact hmask.2 d.1 side d.2 hside hlocal
  change vertexMask d.1 = sixVertexTorusLocalSwitchMask mask d.1 d.2
  cases hvertex : vertexMask d.1 <;>
    cases hedge : sixVertexTorusLocalSwitchMask mask d.1 d.2
  · rfl
  · exact False.elim (by simpa [hvertex] using hselectedToActive hedge)
  · exact False.elim (by simpa [hedge] using hactiveToSelected hvertex)
  · rfl

theorem SixVertexFullDisagreementMask.fullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredFullSwapBondCoherent source
      (sixVertexFullDisagreementVertexMask mask) := by
  intro d hd
  apply (fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq source d).2
  by_contra hedge
  have hdisagrees : sixVertexTorusEdgeDisagrees
      (source false).arrows (source true).arrows
      (sixVertexTorusDartEdge T
        (sixVertexTorusDartOfMedialDart d)) := hedge
  have heq := hmask.vertexMask_bondMate
    (sixVertexTorusDartOfMedialDart d) hdisagrees
  rw [← sixVertexTorusDartOfMedialDart_bondMate] at heq
  exact hd heq


def sixVertexFullDisagreementColoredTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredLoopPairingPair T :=
  fkColoredFullSwapTarget source
    (sixVertexFullDisagreementVertexMask mask)
    (hmask.fullSwapBondCoherent source mask)

theorem sixVertexFullDisagreementColoredTarget_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) (layer : Bool) :
    (sixVertexFullDisagreementColoredTarget source mask hmask layer).arrows =
      if layer then
        sixVertexTorusSwitchSecond mask
          (source false).arrows (source true).arrows
      else sixVertexTorusSwitchFirst mask
          (source false).arrows (source true).arrows := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  cases layer <;> apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_horizontal, Bool.false_eq_true, if_false]
    by_cases hdiff : (source false).arrows.horizontal v ≠
        (source true).arrows.horizontal v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdiff))
      change vertexMask v = mask.horizontal v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchFirst, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_vertical, Bool.false_eq_true, if_false]
    by_cases hdiff : (source false).arrows.vertical v ≠
        (source true).arrows.vertical v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdiff))
      change vertexMask v = mask.vertical v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchFirst, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_horizontal, if_true]
    by_cases hdiff : (source false).arrows.horizontal v ≠
        (source true).arrows.horizontal v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdiff))
      change vertexMask v = mask.horizontal v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchSecond, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_vertical, if_true]
    by_cases hdiff : (source false).arrows.vertical v ≠
        (source true).arrows.vertical v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdiff))
      change vertexMask v = mask.vertical v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchSecond, heq]

theorem sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFullDisagreementColoredTarget
            source mask hmask false).arrows.horizontal,
          (sixVertexFullDisagreementColoredTarget
            source mask hmask true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) := by
  rw [sixVertexFullDisagreementColoredTarget_arrows,
    sixVertexFullDisagreementColoredTarget_arrows]
  exact hmask.boundedFineRowProfile

theorem sixVertexFullDisagreementColoredTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (fkColoredLoopPairingPairTotalC
        (sixVertexFullDisagreementColoredTarget source mask hmask),
      fkColoredTrueStrandSlotCount
        (sixVertexFullDisagreementColoredTarget source mask hmask)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  fkColoredFullSwapTarget_bigrade source _ _

theorem sixVertexFullDisagreementColoredTarget_middleSectors
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (middle : Nat)
    (hlower : sixVertexUpCount
      (svTorusVerticalRows T (source false).arrows
        (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
      (svTorusVerticalRows T (source true).arrows
        (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexFullDisagreementColoredTarget
            source mask hmask false).arrows
          (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexFullDisagreementColoredTarget
            source mask hmask true).arrows
          (svFinLast T.height_pos)) = middle := by
  rw [sixVertexFullDisagreementColoredTarget_arrows,
    sixVertexFullDisagreementColoredTarget_arrows]
  constructor
  · have hcount := intCast_upCount_switchFirst_eq_add_seamTransfer
      mask (source false).arrows (source true).arrows
    rw [hlower, htransfer] at hcount
    have hnat : middle - 1 + 1 = middle :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmiddle.ne')
    rw [← hnat]
    exact_mod_cast hcount
  · have hcount := intCast_upCount_switchSecond_eq_sub_seamTransfer
      mask (source false).arrows (source true).arrows
    rw [hupper, htransfer] at hcount
    have hcast : ((middle + 1 : Nat) : Int) - 1 = (middle : Int) := by
      omega
    rw [hcast] at hcount
    exact_mod_cast hcount



def sixVertexLoopDecoratedFullMaskTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  let target := sixVertexFullDisagreementColoredTarget colored mask hmask
  have hsectors := sixVertexFullDisagreementColoredTarget_middleSectors
    colored mask hmask middle.val
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
    hmiddle_pos htransfer
  exact ⟨(⟨(target false).arrows, (target false).iceRule, hsectors.1⟩,
      ⟨(target true).arrows, (target true).iceRule, hsectors.2⟩),
    (target false).toCompatible, (target true).toCompatible⟩

theorem sixVertexLoopDecoratedFullMaskTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
          source mask hmask htransfer) =
      sixVertexFullDisagreementColoredTarget
        (sixVertexLoopDecoratedPairColored source) mask hmask := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

theorem sixVertexLoopDecoratedFullMaskTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
          source mask hmask htransfer) =
      sixVertexLoopDecoratedPairBigrade source := by
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedFullMaskTarget_colored]
  exact sixVertexFullDisagreementColoredTarget_bigrade _ _ _

end

end StatMech.FrontierD
