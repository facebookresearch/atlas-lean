/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexIndexedOccurrenceSplice
import Code.FrontierD.FKMedialBoundaryToggleParity










namespace StatMech.FrontierD

noncomputable section


def fkColoredBlackDartStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (dart : FKMedialBlackDart T) : T.Vertex × Bool :=
  (dart.1.1, fkColoredSideSlot (pairing dart.1.1) dart.1.2)

theorem fkColoredBlackDartStrandSlot_injective
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Function.Injective (fkColoredBlackDartStrandSlot pairing) := by
  intro first second h
  rcases first with ⟨⟨v, firstSide⟩, hfirst⟩
  rcases second with ⟨⟨w, secondSide⟩, hsecond⟩
  apply Subtype.ext
  have hvw : v = w := congrArg Prod.fst h
  subst w
  apply Prod.ext
  · rfl
  · have hslot := congrArg Prod.snd h
    cases hp : pairing v <;>
      cases hv : fkMedialVertexParity v <;>
      cases firstSide <;> cases secondSide <;>
      simp [fkMedialCheckerColor, fkMedialSideVertical,
        fkColoredBlackDartStrandSlot, fkColoredSideSlot,
        hp, hv] at hfirst hsecond hslot ⊢


noncomputable def fkColoredBlackDartStrandSlotEquiv
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    FKMedialBlackDart T ≃ T.Vertex × Bool :=
  Equiv.ofBijective (fkColoredBlackDartStrandSlot pairing) (by
    apply (Fintype.bijective_iff_injective_and_card
      (fkColoredBlackDartStrandSlot pairing)).2
    refine ⟨fkColoredBlackDartStrandSlot_injective pairing, ?_⟩
    rw [card_fkMedialBlackDart]
    simp [EvenTorus.Vertex]
    ring)

@[simp] theorem fkColoredBlackDartStrandSlotEquiv_apply
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlotEquiv pairing dart =
      fkColoredBlackDartStrandSlot pairing dart := rfl


def fkColoredVertexStrandSlotSwap
    {T : EvenTorus} (v : T.Vertex) :
    Equiv.Perm (T.Vertex × Bool) :=
  Equiv.swap (v, false) (v, true)

theorem fkColoredBlackDartStrandSlot_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlot
        (fkMedialTogglePairingAt pairing v) dart =
      if fkMedialVertexParity v = true then
        fkColoredVertexStrandSlotSwap v
          (fkColoredBlackDartStrandSlot pairing dart)
      else fkColoredBlackDartStrandSlot pairing dart := by
  rcases dart with ⟨⟨w, side⟩, hdart⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;> cases hv : fkMedialVertexParity v <;>
      cases side <;>
      simp [fkColoredBlackDartStrandSlot,
        fkColoredVertexStrandSlotSwap, fkColoredSideSlot,
        fkMedialTogglePairingAt, hp, fkMedialCheckerColor,
        fkMedialSideVertical, hv] at hdart ⊢
  · have hfalse :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, false) := by
      intro h
      exact hw (congrArg Prod.fst h)
    have htrue :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, true) := by
      intro h
      exact hw (congrArg Prod.fst h)
    simp [fkColoredBlackDartStrandSlot,
      fkColoredVertexStrandSlotSwap, fkMedialTogglePairingAt, hw,
      Equiv.swap_apply_of_ne_of_ne hfalse htrue]

theorem fkColoredBlackDartStrandSlotEquiv_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    fkColoredBlackDartStrandSlotEquiv
        (fkMedialTogglePairingAt pairing v) =
      if fkMedialVertexParity v = true then
        (fkColoredBlackDartStrandSlotEquiv pairing).trans
          (fkColoredVertexStrandSlotSwap v)
      else fkColoredBlackDartStrandSlotEquiv pairing := by
  apply Equiv.ext
  intro dart
  rw [fkColoredBlackDartStrandSlotEquiv_apply]
  by_cases hv : fkMedialVertexParity v = true
  · rw [if_pos hv]
    simp only [Equiv.trans_apply,
      fkColoredBlackDartStrandSlotEquiv_apply]
    simpa [hv] using
      fkColoredBlackDartStrandSlot_toggle pairing v dart
  · rw [if_neg hv]
    simpa [hv] using
      fkColoredBlackDartStrandSlot_toggle pairing v dart

theorem fkColoredBlackDartStrandSlot_blackSwap
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartSwap v dart) =
      fkColoredVertexStrandSlotSwap v
        (fkColoredBlackDartStrandSlotEquiv pairing dart) := by
  rcases dart with ⟨⟨w, side⟩, hdart⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;> cases hv : fkMedialVertexParity v <;>
      cases side <;>
      simp [fkColoredBlackDartStrandSlotEquiv_apply,
        fkColoredBlackDartStrandSlot, fkMedialBlackDartSwap,
        fkMedialBlackDart0, fkMedialBlackDart1,
        fkColoredVertexStrandSlotSwap, fkColoredSideSlot,
        fkMedialCheckerColor, fkMedialSideVertical, hp, hv] at hdart ⊢
  · have hzero : (⟨⟨w, side⟩, hdart⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart0 v := by
      intro h
      exact hw (congrArg (fun d : FKMedialBlackDart T => d.1.1) h)
    have hone : (⟨⟨w, side⟩, hdart⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart1 v := by
      intro h
      exact hw (congrArg (fun d : FKMedialBlackDart T => d.1.1) h)
    have hfalse :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, false) := by
      intro h
      exact hw (congrArg Prod.fst h)
    have htrue :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, true) := by
      intro h
      exact hw (congrArg Prod.fst h)
    simp [fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkMedialBlackDartSwap,
      fkColoredVertexStrandSlotSwap,
      Equiv.swap_apply_of_ne_of_ne hzero hone,
      Equiv.swap_apply_of_ne_of_ne hfalse htrue]


noncomputable def fkColoredStrandSlotBoundaryPerm
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Equiv.Perm (T.Vertex × Bool) :=
  (fkColoredBlackDartStrandSlotEquiv pairing).symm.trans
    ((fkMedialBlackBoundaryPerm pairing).trans
      (fkColoredBlackDartStrandSlotEquiv pairing))




theorem fkColoredStrandSlotBoundaryPerm_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    fkColoredStrandSlotBoundaryPerm
        (fkMedialTogglePairingAt pairing v) =
      if fkMedialVertexParity v = true then
        (fkColoredStrandSlotBoundaryPerm pairing).trans
          (fkColoredVertexStrandSlotSwap v)
      else
        (fkColoredVertexStrandSlotSwap v).trans
          (fkColoredStrandSlotBoundaryPerm pairing) := by
  apply Equiv.ext
  intro slot
  by_cases hv : fkMedialVertexParity v = true
  · rw [if_pos hv]
    have hcoordinate :
        fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingAt pairing v) =
          (fkColoredBlackDartStrandSlotEquiv pairing).trans
            (fkColoredVertexStrandSlotSwap v) := by
      rw [fkColoredBlackDartStrandSlotEquiv_toggle, if_pos hv]
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
    rw [fkMedialBlackBoundaryPerm_toggle, hcoordinate]
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
    have hcancel : fkMedialBlackDartSwap v
        (((fkColoredBlackDartStrandSlotEquiv pairing).trans
          (fkColoredVertexStrandSlotSwap v)).symm slot) =
        (fkColoredBlackDartStrandSlotEquiv pairing).symm slot := by
      apply (fkColoredBlackDartStrandSlotEquiv pairing).injective
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simp
    rw [hcancel]
  · rw [if_neg hv]
    have hcoordinate :
        fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingAt pairing v) =
          fkColoredBlackDartStrandSlotEquiv pairing := by
      rw [fkColoredBlackDartStrandSlotEquiv_toggle, if_neg hv]
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
    rw [fkMedialBlackBoundaryPerm_toggle, hcoordinate]
    simp only [Equiv.Perm.mul_apply]
    have hinput : fkMedialBlackDartSwap v
        ((fkColoredBlackDartStrandSlotEquiv pairing).symm slot) =
        (fkColoredBlackDartStrandSlotEquiv pairing).symm
          (fkColoredVertexStrandSlotSwap v slot) := by
      apply (fkColoredBlackDartStrandSlotEquiv pairing).injective
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simp
    rw [hinput]

theorem FKColoredLoopPairing.color_blackDart_eq_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (source layer).color dart.1 =
      fkColoredLayeredSlotColor source
        (layer, fkColoredBlackDartStrandSlotEquiv
          (source layer).pairing dart) := by
  simpa [fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot] using
      FKColoredLoopPairing.color_eq_slotColor source
        layer dart.1.1 dart.1.2



theorem FKColoredLoopPairing.slotColor_boundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (slot : T.Vertex × Bool) :
    fkColoredLayeredSlotColor source
        (layer, fkColoredStrandSlotBoundaryPerm
          (source layer).pairing slot) =
      fkColoredLayeredSlotColor source (layer, slot) := by
  let coordinate := fkColoredBlackDartStrandSlotEquiv
    (source layer).pairing
  let dart := coordinate.symm slot
  have hdart : coordinate dart = slot := coordinate.apply_symm_apply slot
  have hboundary :
      (source layer).color
          (fkMedialBlackBoundaryPerm (source layer).pairing dart).1 =
        (source layer).color dart.1 := by
    exact ((source layer).color_bondMate
      (fkMedialLocalMate (source layer).pairing dart.1)).trans
        ((source layer).color_localMate dart.1)
  change fkColoredLayeredSlotColor source
      (layer, coordinate
        (fkMedialBlackBoundaryPerm (source layer).pairing dart)) =
    fkColoredLayeredSlotColor source (layer, slot)
  rw [← hdart]
  rw [← FKColoredLoopPairing.color_blackDart_eq_slotColor
      source layer,
    ← FKColoredLoopPairing.color_blackDart_eq_slotColor source layer]
  exact hboundary


noncomputable def fkColoredLayeredStrandSlotBoundaryPerm
    {T : EvenTorus} (pairing : Bool -> FKMedialLoopPairing T) :
    Equiv.Perm (FKLayeredStrandSlot T) where
  toFun slot :=
    (slot.1, fkColoredStrandSlotBoundaryPerm (pairing slot.1) slot.2)
  invFun slot :=
    (slot.1,
      (fkColoredStrandSlotBoundaryPerm (pairing slot.1)).symm slot.2)
  left_inv slot := by simp
  right_inv slot := by simp

@[simp] theorem fkColoredLayeredStrandSlotBoundaryPerm_apply
    {T : EvenTorus} (pairing : Bool -> FKMedialLoopPairing T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredStrandSlotBoundaryPerm pairing slot =
      (slot.1,
        fkColoredStrandSlotBoundaryPerm (pairing slot.1) slot.2) := rfl

theorem fkColoredLayeredSlotColor_boundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor source
        (fkColoredLayeredStrandSlotBoundaryPerm
          (fun layer => (source layer).pairing) slot) =
      fkColoredLayeredSlotColor source slot := by
  rcases slot with ⟨layer, slot⟩
  exact FKColoredLoopPairing.slotColor_boundaryPerm source layer slot



def FKColoredIndexedOccurrenceSlotIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall slot : FKLayeredStrandSlot T,
    fkIndexedOccurrenceSlotEquiv n key hinjective
        (fkColoredLayeredStrandSlotBoundaryPerm targetPairing slot) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer => (source layer).pairing)
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot)





def FKColoredIndexedOccurrenceSlotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall slot : FKLayeredStrandSlot T,
    fkColoredLayeredSlotColor source
        (fkIndexedOccurrenceSlotEquiv n key hinjective
          (fkColoredLayeredStrandSlotBoundaryPerm targetPairing slot)) =
      fkColoredLayeredSlotColor source
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot)



theorem fkColoredStrandSpliceRawColor_blackDart
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, dart.1) =
      fkColoredLayeredSlotColor source
        (slotEquiv (layer,
          fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer) dart)) := by
  simp [fkColoredStrandSpliceRawColor,
    fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot]



theorem fkColoredStrandSpliceRawColor_blackBoundary
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, (fkMedialBlackBoundaryPerm
          (targetPairing layer) dart).1) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, dart.1) := by
  rw [fkColoredStrandSpliceRawColor_blackDart,
    fkColoredStrandSpliceRawColor_blackDart]
  let slot : FKLayeredStrandSlot T :=
    (layer, fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer) dart)
  have hstep : fkColoredLayeredStrandSlotBoundaryPerm
      targetPairing slot =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer) dart)) := by
    change (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer)
          ((fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer)).symm
            (fkColoredBlackDartStrandSlotEquiv
              (targetPairing layer) dart)))) = _
    rw [(fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer)).symm_apply_apply]
  rw [← hstep, hintertwines]
  exact fkColoredLayeredSlotColor_boundaryPerm source
    (fkIndexedOccurrenceSlotEquiv n key hinjective slot)



theorem fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, (fkMedialBlackBoundaryPerm
          (targetPairing layer) dart).1) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, dart.1) := by
  rw [fkColoredStrandSpliceRawColor_blackDart,
    fkColoredStrandSpliceRawColor_blackDart]
  let slot : FKLayeredStrandSlot T :=
    (layer, fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer) dart)
  have hstep : fkColoredLayeredStrandSlotBoundaryPerm
      targetPairing slot =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer) dart)) := by
    change (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer)
          ((fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer)).symm
            (fkColoredBlackDartStrandSlotEquiv
              (targetPairing layer) dart)))) = _
    rw [(fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer)).symm_apply_apply]
  rw [← hstep]
  exact hinvariant slot



theorem coloredIndexedOccurrenceBoundaryIntertwining_of_slot
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective := by
  intro x
  rcases x with ⟨layer, dart⟩
  by_cases hblack : fkMedialCheckerColor dart = false
  · let blackDart : FKMedialBlackDart T := ⟨dart, hblack⟩
    simpa [blackDart, fkMedialBlackBoundaryPerm_val_step] using
      fkColoredStrandSpliceRawColor_blackBoundary source targetPairing
        n key hinjective hintertwines layer blackDart
  · have hwhite : fkMedialCheckerColor dart = true := by
      cases h : fkMedialCheckerColor dart <;> simp_all
    let boundary := fkMedialBoundaryStep (targetPairing layer) dart
    have hboundaryWhite : fkMedialCheckerColor boundary = true := by
      simpa [boundary, hwhite] using
        fkMedialCheckerColor_boundaryStep (targetPairing layer) dart
    have hpreBlack : fkMedialCheckerColor
        (fkMedialLocalMate (targetPairing layer) boundary) = false := by
      have hne := fkMedialCheckerColor_localMate_ne
        (targetPairing layer) boundary
      cases h : fkMedialCheckerColor
          (fkMedialLocalMate (targetPairing layer) boundary) <;>
        simp_all
    let predecessor : FKMedialBlackDart T :=
      ⟨fkMedialLocalMate (targetPairing layer) boundary, hpreBlack⟩
    have hnext : fkMedialBlackBoundaryPerm
        (targetPairing layer) predecessor =
      (⟨fkMedialLocalMate (targetPairing layer) dart, by
        have hne := fkMedialCheckerColor_localMate_ne
          (targetPairing layer) dart
        cases h : fkMedialCheckerColor
            (fkMedialLocalMate (targetPairing layer) dart) <;>
          simp_all⟩ : FKMedialBlackDart T) := by
      apply Subtype.ext
      simp [predecessor, boundary, fkMedialBoundaryStep_apply,
        fkMedialLocalMate_involutive,
        fkMedialBondMate_involutive]
    have hroute := fkColoredStrandSpliceRawColor_blackBoundary
      source targetPairing n key hinjective hintertwines layer predecessor
    rw [hnext] at hroute
    have hlocalDart := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer dart
    have hlocalBoundary := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer boundary
    exact hlocalBoundary.symm.trans (hroute.symm.trans hlocalDart)



theorem coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective := by
  intro x
  rcases x with ⟨layer, dart⟩
  by_cases hblack : fkMedialCheckerColor dart = false
  · let blackDart : FKMedialBlackDart T := ⟨dart, hblack⟩
    simpa [blackDart, fkMedialBlackBoundaryPerm_val_step] using
      fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
        source targetPairing n key hinjective hinvariant layer blackDart
  · have hwhite : fkMedialCheckerColor dart = true := by
      cases h : fkMedialCheckerColor dart <;> simp_all
    let boundary := fkMedialBoundaryStep (targetPairing layer) dart
    have hboundaryWhite : fkMedialCheckerColor boundary = true := by
      simpa [boundary, hwhite] using
        fkMedialCheckerColor_boundaryStep (targetPairing layer) dart
    have hpreBlack : fkMedialCheckerColor
        (fkMedialLocalMate (targetPairing layer) boundary) = false := by
      have hne := fkMedialCheckerColor_localMate_ne
        (targetPairing layer) boundary
      cases h : fkMedialCheckerColor
          (fkMedialLocalMate (targetPairing layer) boundary) <;>
        simp_all
    let predecessor : FKMedialBlackDart T :=
      ⟨fkMedialLocalMate (targetPairing layer) boundary, hpreBlack⟩
    have hnext : fkMedialBlackBoundaryPerm
        (targetPairing layer) predecessor =
      (⟨fkMedialLocalMate (targetPairing layer) dart, by
        have hne := fkMedialCheckerColor_localMate_ne
          (targetPairing layer) dart
        cases h : fkMedialCheckerColor
            (fkMedialLocalMate (targetPairing layer) dart) <;>
          simp_all⟩ : FKMedialBlackDart T) := by
      apply Subtype.ext
      simp [predecessor, boundary, fkMedialBoundaryStep_apply,
        fkMedialLocalMate_involutive,
        fkMedialBondMate_involutive]
    have hroute :=
      fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
        source targetPairing n key hinjective hinvariant layer predecessor
    rw [hnext] at hroute
    have hlocalDart := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer dart
    have hlocalBoundary := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer boundary
    exact hlocalBoundary.symm.trans (hroute.symm.trans hlocalDart)



def FKColoredStrandSplice.ofIndexedSlotIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
    n key hinjective
      (coloredIndexedOccurrenceBoundaryIntertwining_of_slot
        source targetPairing n key hinjective hintertwines)



theorem coloredIndexedOccurrenceSlotIntertwining_of_successor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (next : Fin n -> Fin n)
    (htarget : forall layer i,
      fkColoredStrandSlotBoundaryPerm (targetPairing layer)
          (key layer i) = key layer (next i))
    (hsource : forall layer i,
      fkColoredStrandSlotBoundaryPerm (source layer).pairing
          (key layer i) = key layer (next i))
    (hfixed : forall layer slot,
      (¬ exists i, key layer i = slot) ->
      fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot =
          fkColoredStrandSlotBoundaryPerm (source layer).pairing slot /\
        (¬ exists i, key layer i =
          fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot)) :
    FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  by_cases hselected : exists i, key layer i = slot
  · obtain ⟨i, rfl⟩ := hselected
    change fkIndexedOccurrenceSlotEquiv n key hinjective
        (layer, fkColoredStrandSlotBoundaryPerm
          (targetPairing layer) (key layer i)) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer => (source layer).pairing)
        (fkIndexedOccurrenceSlotEquiv n key hinjective
          (layer, key layer i))
    rw [htarget,
      fkIndexedOccurrenceSlotEquiv_apply_key,
      fkIndexedOccurrenceSlotEquiv_apply_key]
    change (!layer, key (!layer) (next i)) =
      (!layer, fkColoredStrandSlotBoundaryPerm
        (source (!layer)).pairing (key (!layer) i))
    rw [hsource]
  · have hfix := hfixed layer slot hselected
    have houtput : ¬ exists i, key layer i =
        fkColoredStrandSlotBoundaryPerm (source layer).pairing slot := by
      rw [← hfix.1]
      exact hfix.2
    rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
      hfix.1,
      fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
        n key hinjective (layer, slot)]
    · rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
      fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
          n key hinjective]
      simpa using houtput
    · simpa using hselected

end

end StatMech.FrontierD
