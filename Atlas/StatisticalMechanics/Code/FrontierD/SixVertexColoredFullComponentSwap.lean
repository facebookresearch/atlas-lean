/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand











namespace StatMech.FrontierD

noncomputable section

local instance sixVertexColoredFullComponentSwapPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


def sixVertexFinSideOfMedialSide : FKMedialSide -> Fin 4
  | .west => 0
  | .east => 1
  | .south => 2
  | .north => 3

def sixVertexTorusDartOfMedialDart
    {T : EvenTorus} (d : FKMedialDart T) : SixVertexTorusDart T :=
  (d.1, sixVertexFinSideOfMedialSide d.2)

theorem sixVertexTorusDartOfMedialDart_bondMate
    (T : EvenTorus) (d : FKMedialDart T) :
    sixVertexTorusDartOfMedialDart (fkMedialBondMate T d) =
      sixVertexTorusDartBondMate T
        (sixVertexTorusDartOfMedialDart d) := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;> rfl

theorem fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (d : FKMedialDart T) :
    (source false).color d = (source true).color d ↔
      sixVertexTorusEdgeArrow (source false).arrows
          (sixVertexTorusDartEdge T
            (sixVertexTorusDartOfMedialDart d)) =
        sixVertexTorusEdgeArrow (source true).arrows
          (sixVertexTorusDartEdge T
            (sixVertexTorusDartOfMedialDart d)) := by
  rcases d with ⟨v, side⟩
  have hfalse := (source false).dartIncoming_arrows (v, side)
  have htrue := (source true).dartIncoming_arrows (v, side)
  calc
    (source false).color (v, side) = (source true).color (v, side) ↔
        (source false).incoming (v, side) =
          (source true).incoming (v, side) := by
      unfold FKColoredLoopPairing.incoming
      generalize hc : fkMedialCheckerColor (v, side) = c
      generalize hf : (source false).color (v, side) = f
      generalize ht : (source true).color (v, side) = t
      cases c <;> cases f <;> cases t <;> simp
    _ ↔ fkMedialDartIncoming (source false).arrows (v, side) =
        fkMedialDartIncoming (source true).arrows (v, side) := by
      rw [hfalse, htrue]
    _ ↔ _ := by
      cases side <;>
        simp [sixVertexTorusDartEdge, sixVertexTorusDartOfMedialDart,
          sixVertexFinSideOfMedialSide, sixVertexTorusIncidentEdge,
          sixVertexTorusEdgeArrow, fkMedialDartIncoming,
          fkLoopWestIncoming, fkLoopEastIncoming,
          fkLoopSouthIncoming, fkLoopNorthIncoming]



def FKColoredFullSwapBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) : Prop :=
  forall d : FKMedialDart T,
    mask d.1 ≠ mask (fkMedialBondMate T d).1 ->
      (source false).color d = (source true).color d



def fkColoredFullSwapTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := fun v =>
      if mask v then (source (!layer)).pairing v
      else (source layer).pairing v
    color := fun d =>
      if mask d.1 then (source (!layer)).color d
      else (source layer).color d
    color_localMate := by
      rintro ⟨v, side⟩
      by_cases hm : mask v
      · simp only [hm, if_true, fkMedialLocalMate_eq_localSideMate]
        simpa only [fkMedialLocalMate_eq_localSideMate] using
          (source (!layer)).color_localMate (v, side)
      · simp only [hm, if_false, fkMedialLocalMate_eq_localSideMate]
        simpa only [fkMedialLocalMate_eq_localSideMate] using
          (source layer).color_localMate (v, side)
    color_bondMate := by
      intro d
      by_cases hd : mask d.1 <;>
        by_cases hm : mask (fkMedialBondMate T d).1
      · simp only [hd, hm, if_true]
        exact (source (!layer)).color_bondMate d
      · have hcross := hbond d (by simp [hd, hm])
        simp only [hd, hm, if_true, if_false]
        rw [(source layer).color_bondMate d]
        cases layer
        · simpa using hcross
        · simpa using hcross.symm
      · have hcross := hbond d (by simp [hd, hm])
        simp only [hd, hm, if_true, if_false]
        rw [(source (!layer)).color_bondMate d]
        cases layer
        · simpa using hcross.symm
        · simpa using hcross
      · simp only [hd, hm, if_false]
        exact (source layer).color_bondMate d }

@[simp] theorem fkColoredFullSwapTarget_pairing
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).pairing v =
      if mask v then (source (!layer)).pairing v
      else (source layer).pairing v := rfl

@[simp] theorem fkColoredFullSwapTarget_color
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (d : FKMedialDart T) :
    (fkColoredFullSwapTarget source mask hbond layer).color d =
      if mask d.1 then (source (!layer)).color d
      else (source layer).color d := rfl

@[simp] theorem fkColoredFullSwapTarget_horizontal
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).arrows.horizontal v =
      if mask v then (source (!layer)).arrows.horizontal v
      else (source layer).arrows.horizontal v := by
  cases layer <;> by_cases hm : mask v <;>
    simp [FKColoredLoopPairing.arrows, FKColoredLoopPairing.incoming,
      fkColoredFullSwapTarget, hm]

@[simp] theorem fkColoredFullSwapTarget_vertical
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (layer : Bool) (v : T.Vertex) :
    (fkColoredFullSwapTarget source mask hbond layer).arrows.vertical v =
      if mask v then (source (!layer)).arrows.vertical v
      else (source layer).arrows.vertical v := by
  cases layer <;> by_cases hm : mask v <;>
    simp [FKColoredLoopPairing.arrows, FKColoredLoopPairing.incoming,
      fkColoredFullSwapTarget, hm]

theorem fkColoredFullSwapTarget_bondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    FKColoredFullSwapBondCoherent
      (fkColoredFullSwapTarget source mask hbond) mask := by
  intro d hmask
  have hsource := hbond d hmask
  by_cases hd : mask d.1 = true
  · simp [fkColoredFullSwapTarget_color, hd, hsource]
  · have hdfalse : mask d.1 = false := Bool.eq_false_of_not_eq_true hd
    simp [fkColoredFullSwapTarget_color, hdfalse, hsource]

@[simp] theorem fkColoredFullSwapTarget_involutive
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredFullSwapTarget
        (fkColoredFullSwapTarget source mask hbond) mask
        (fkColoredFullSwapTarget_bondCoherent source mask hbond) = source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : mask v <;> cases layer <;> simp [hm]
  · funext d
    by_cases hm : mask d.1 <;> cases layer <;> simp [hm]


def fkColoredFullSwapLayeredSlotEquiv
    {T : EvenTorus} (mask : T.Vertex -> Bool) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T where
  toFun slot := (if mask slot.2.1 then !slot.1 else slot.1, slot.2)
  invFun slot := (if mask slot.2.1 then !slot.1 else slot.1, slot.2)
  left_inv slot := by
    rcases slot with ⟨layer, v, side⟩
    by_cases hm : mask v <;> cases layer <;> simp [hm]
  right_inv slot := by
    rcases slot with ⟨layer, v, side⟩
    by_cases hm : mask v <;> cases layer <;> simp [hm]

theorem fkColoredFullSwapTarget_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (fkColoredFullSwapTarget source mask hbond) slot =
      fkColoredLayeredSlotColor source
        (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
  rcases slot with ⟨layer, v, side⟩
  by_cases hm : mask v <;> cases layer <;> cases side <;>
    simp [fkColoredLayeredSlotColor, fkColoredFullSwapLayeredSlotEquiv,
      fkColoredFullSwapTarget, hm]

theorem fkColoredFullSwapTarget_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredTrueStrandSlotCount
        (fkColoredFullSwapTarget source mask hbond) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (fkColoredFullSwapLayeredSlotEquiv mask)
  intro slot
  rw [fkColoredFullSwapTarget_slotColor]

theorem fkColoredFullSwapTarget_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredLoopPairingPairTotalC
        (fkColoredFullSwapTarget source mask hbond) =
      fkColoredLoopPairingPairTotalC source := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
  rw [<- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(fkColoredFullSwapTarget source mask hbond false).cType_iff_color_west_eq_east,
    (fkColoredFullSwapTarget source mask hbond true).cType_iff_color_west_eq_east,
    (source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hm : mask v <;>
    by_cases hw : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases ht : (source true).color (v, .west) =
      (source true).color (v, .east) <;>
    simp [fkColoredFullSwapTarget, hm, add_comm, hw, ht]

theorem fkColoredFullSwapTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    (fkColoredLoopPairingPairTotalC
        (fkColoredFullSwapTarget source mask hbond),
      fkColoredTrueStrandSlotCount
        (fkColoredFullSwapTarget source mask hbond)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  rw [fkColoredFullSwapTarget_totalC,
    fkColoredFullSwapTarget_trueStrandSlotCount]

end

end StatMech.FrontierD
