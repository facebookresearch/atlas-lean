/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredFullComponentSwap










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexLexComponentColoredSwapPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

def sixVertexTorusEdgeMaskVertexMask
    {T : EvenTorus} (edgeMask : SixVertexArrows T) (v : T.Vertex) : Bool :=
  decide (∃ side : Fin 4,
    sixVertexTorusLocalSwitchMask edgeMask v side = true)

theorem sixVertexTorusEdgeMaskVertexMask_eq_true_iff
    {T : EvenTorus} (edgeMask : SixVertexArrows T) (v : T.Vertex) :
    sixVertexTorusEdgeMaskVertexMask edgeMask v = true ↔
      ∃ side : Fin 4,
        sixVertexTorusLocalSwitchMask edgeMask v side = true := by
  simp [sixVertexTorusEdgeMaskVertexMask]

theorem sixVertexTorusLocalSwitchMask_bondMate
    {T : EvenTorus} (edgeMask : SixVertexArrows T)
    (d : SixVertexTorusDart T) :
    sixVertexTorusLocalSwitchMask edgeMask
        (sixVertexTorusDartBondMate T d).1
        (sixVertexTorusDartBondMate T d).2 =
      sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 := by
  rw [sixVertexTorusLocalSwitchMask_apply,
    sixVertexTorusLocalSwitchMask_apply]
  exact congrArg (sixVertexTorusMaskSelects edgeMask)
    (sixVertexTorusDartEdge_bondMate T d)

def sixVertexLexDisagreementComponentVertexMask
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    T.Vertex -> Bool :=
  sixVertexTorusEdgeMaskVertexMask
    (sixVertexLexDisagreementComponentMask T omega eta h)

theorem sixVertexLexDisagreementComponentVertexMask_bondMate
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 =
      sixVertexLexDisagreementComponentVertexMask T omega eta h
        (sixVertexTorusDartBondMate T d).1 := by
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  have hlocalDisagrees : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hforward (hselected : vertexMask d.1 = true) :
      vertexMask (sixVertexTorusDartBondMate T d).1 = true := by
    have hactive : ∃ side,
        sixVertexTorusLocalSwitchMask edgeMask d.1 side = true :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).1
        hselected
    obtain ⟨side, hside⟩ := hactive
    have hdSelected : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true :=
      sixVertexLexDisagreementComponentMask_incident_closure
        T omega eta h d.1 side d.2 hside hlocalDisagrees
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask _).2
    exact ⟨(sixVertexTorusDartBondMate T d).2, by
      rw [sixVertexTorusLocalSwitchMask_bondMate edgeMask d]
      exact hdSelected⟩
  have hreverse
      (hselected : vertexMask (sixVertexTorusDartBondMate T d).1 = true) :
      vertexMask d.1 = true := by
    let mate := sixVertexTorusDartBondMate T d
    have hedgeMate : sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusDartEdge T mate) := by
      rw [sixVertexTorusDartEdge_bondMate]
      exact hdisagrees
    have hlocalMate : sixVertexLocalIncomingPattern omega mate.1 mate.2 ≠
        sixVertexLocalIncomingPattern eta mate.1 mate.2 :=
      (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
        omega eta mate.1 mate.2).2 hedgeMate
    have hactive : ∃ side,
        sixVertexTorusLocalSwitchMask edgeMask mate.1 side = true :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask mate.1).1
        hselected
    obtain ⟨side, hside⟩ := hactive
    have hmateSelected :
        sixVertexTorusLocalSwitchMask edgeMask mate.1 mate.2 = true :=
      sixVertexLexDisagreementComponentMask_incident_closure
        T omega eta h mate.1 side mate.2 hside hlocalMate
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).2
    refine ⟨d.2, ?_⟩
    rw [← sixVertexTorusLocalSwitchMask_bondMate edgeMask d]
    exact hmateSelected
  change vertexMask d.1 = vertexMask (sixVertexTorusDartBondMate T d).1
  cases hfirst : vertexMask d.1 <;>
    cases hsecond : vertexMask (sixVertexTorusDartBondMate T d).1
  · rfl
  · exact False.elim (by
      have := hreverse hsecond
      simp [hfirst] at this)
  · exact False.elim (by
      have := hforward hfirst
      simp [hsecond] at this)
  · rfl

theorem sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (d : SixVertexTorusDart T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusDartEdge T d)) :
    sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 =
      sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) d.1 d.2 := by
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  have hlocalDisagrees : sixVertexLocalIncomingPattern omega d.1 d.2 ≠
      sixVertexLocalIncomingPattern eta d.1 d.2 :=
    (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta d.1 d.2).2 hdisagrees
  have hselectedToActive
      (hselected : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true) :
      vertexMask d.1 = true := by
    apply (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).2
    exact ⟨d.2, hselected⟩
  have hactiveToSelected (hactive : vertexMask d.1 = true) :
      sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 = true := by
    obtain ⟨side, hside⟩ :=
      (sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask d.1).1 hactive
    exact sixVertexLexDisagreementComponentMask_incident_closure
      T omega eta h d.1 side d.2 hside hlocalDisagrees
  change vertexMask d.1 =
    sixVertexTorusLocalSwitchMask edgeMask d.1 d.2
  cases hvertex : vertexMask d.1 <;>
    cases hedge : sixVertexTorusLocalSwitchMask edgeMask d.1 d.2
  · rfl
  · exact False.elim (by
      have := hselectedToActive hedge
      simp [hvertex] at this)
  · exact False.elim (by
      have := hactiveToSelected hvertex
      simp [hedge] at this)
  · rfl

theorem sixVertexLexDisagreementComponent_fullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    FKColoredFullSwapBondCoherent source
      (sixVertexLexDisagreementComponentVertexMask T
        (source false).arrows (source true).arrows h) := by
  intro d hmask
  apply (fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq source d).2
  by_contra hedge
  have hdisagrees : sixVertexTorusEdgeDisagrees
      (source false).arrows (source true).arrows
      (sixVertexTorusDartEdge T
        (sixVertexTorusDartOfMedialDart d)) := hedge
  have heq := sixVertexLexDisagreementComponentVertexMask_bondMate
    T (source false).arrows (source true).arrows h
    (sixVertexTorusDartOfMedialDart d) hdisagrees
  rw [← sixVertexTorusDartOfMedialDart_bondMate] at heq
  exact hmask heq


def sixVertexLexDisagreementComponentColoredTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    FKColoredLoopPairingPair T :=
  fkColoredFullSwapTarget source
    (sixVertexLexDisagreementComponentVertexMask T
      (source false).arrows (source true).arrows h)
    (sixVertexLexDisagreementComponent_fullSwapBondCoherent source h)

theorem sixVertexLexDisagreementComponentColoredTarget_false_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    (sixVertexLexDisagreementComponentColoredTarget source h false).arrows =
      sixVertexTorusSwitchFirst
        (sixVertexLexDisagreementComponentMask T
          (source false).arrows (source true).arrows h)
        (source false).arrows (source true).arrows := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_horizontal]
    change (if vertexMask v then eta.horizontal v else omega.horizontal v) = _
    unfold sixVertexTorusSwitchFirst
    by_cases hdisagrees : omega.horizontal v ≠ eta.horizontal v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdisagrees))
      change vertexMask v = edgeMask.horizontal v at hmask
      rw [hmask]
    · have heq : omega.horizontal v = eta.horizontal v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_vertical]
    change (if vertexMask v then eta.vertical v else omega.vertical v) = _
    unfold sixVertexTorusSwitchFirst
    by_cases hdisagrees : omega.vertical v ≠ eta.vertical v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdisagrees))
      change vertexMask v = edgeMask.vertical v at hmask
      rw [hmask]
    · have heq : omega.vertical v = eta.vertical v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]

theorem sixVertexLexDisagreementComponentColoredTarget_true_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    (sixVertexLexDisagreementComponentColoredTarget source h true).arrows =
      sixVertexTorusSwitchSecond
        (sixVertexLexDisagreementComponentMask T
          (source false).arrows (source true).arrows h)
        (source false).arrows (source true).arrows := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_horizontal]
    change (if vertexMask v then omega.horizontal v else eta.horizontal v) = _
    unfold sixVertexTorusSwitchSecond
    by_cases hdisagrees : omega.horizontal v ≠ eta.horizontal v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdisagrees))
      change vertexMask v = edgeMask.horizontal v at hmask
      rw [hmask]
    · have heq : omega.horizontal v = eta.horizontal v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_vertical]
    change (if vertexMask v then omega.vertical v else eta.vertical v) = _
    unfold sixVertexTorusSwitchSecond
    by_cases hdisagrees : omega.vertical v ≠ eta.vertical v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdisagrees))
      change vertexMask v = edgeMask.vertical v at hmask
      rw [hmask]
    · have heq : omega.vertical v = eta.vertical v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]




theorem sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (middle : Nat)
    (hlower : sixVertexUpCount
      (svTorusVerticalRows T (source false).arrows
        (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
      (svTorusVerticalRows T (source true).arrows
        (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty)
    (htransfer : sixVertexTorusMaskSeamTransfer
      (sixVertexLexDisagreementComponentMask T
        (source false).arrows (source true).arrows h)
      (source false).arrows (source true).arrows = 1) :
    let target := sixVertexLexDisagreementComponentColoredTarget source h
    sixVertexUpCount
          (svTorusVerticalRows T (target false).arrows
            (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
          (svTorusVerticalRows T (target true).arrows
            (svFinLast T.height_pos)) = middle /\
      sixVertexHorizontalPairBoundedFineRowProfile
          ((target false).arrows.horizontal,
            (target true).arrows.horizontal) =
        sixVertexHorizontalPairBoundedFineRowProfile
          ((source false).arrows.horizontal,
            (source true).arrows.horizontal) := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let target := sixVertexLexDisagreementComponentColoredTarget source h
  have hmiddleSectors :=
    sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one
      T omega eta middle (source false).iceRule (source true).iceRule
      hlower hupper hmiddle h htransfer
  dsimp only at hmiddleSectors ⊢
  rw [sixVertexLexDisagreementComponentColoredTarget_false_arrows,
    sixVertexLexDisagreementComponentColoredTarget_true_arrows]
  refine ⟨hmiddleSectors.2.2.1, hmiddleSectors.2.2.2, ?_⟩
  exact sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile
    T omega eta h

end

end StatMech.FrontierD
