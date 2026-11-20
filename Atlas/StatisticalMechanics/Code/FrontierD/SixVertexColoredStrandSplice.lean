/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredLoopPairing











open Finset

namespace StatMech.FrontierD

noncomputable section


abbrev FKLayeredStrandSlot (T : EvenTorus) :=
  Bool × T.Vertex × Bool

def fkColoredLayeredSlotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) : Bool :=
  if slot.2.2 then (source slot.1).color (slot.2.1, .east)
  else (source slot.1).color (slot.2.1, .west)


def fkColoredSideSlot (pairing : Bool) (side : FKMedialSide) : Bool :=
  match pairing, side with
  | false, .west | false, .north => false
  | false, .east | false, .south => true
  | true, .west | true, .south => false
  | true, .east | true, .north => true

@[simp] theorem fkColoredSideSlot_west (pairing : Bool) :
    fkColoredSideSlot pairing .west = false := by
  cases pairing <;> rfl

@[simp] theorem fkColoredSideSlot_east (pairing : Bool) :
    fkColoredSideSlot pairing .east = true := by
  cases pairing <;> rfl

theorem fkColoredSideSlot_localMate
    (pairing : Bool) (side : FKMedialSide) :
    fkColoredSideSlot pairing (fkMedialLocalSideMate pairing side) =
      fkColoredSideSlot pairing side := by
  cases pairing <;> cases side <;> rfl

theorem FKColoredLoopPairing.color_eq_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (v : T.Vertex) (side : FKMedialSide) :
    (source layer).color (v, side) =
      fkColoredLayeredSlotColor source
        (layer, v, fkColoredSideSlot ((source layer).pairing v) side) := by
  cases hp : (source layer).pairing v
  · cases side
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .east)
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .west)
  · cases side
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .west)
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .east)



def fkColoredStrandSpliceRawColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (x : FKLayeredMedialDart T) : Bool :=
  fkColoredLayeredSlotColor source
    (slotEquiv (x.1, x.2.1,
      fkColoredSideSlot (targetPairing x.1 x.2.1) x.2.2))

theorem fkColoredStrandSpliceRawColor_localMate
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (layer : Bool) (d : FKMedialDart T) :
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, fkMedialLocalMate (targetPairing layer) d) =
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, d) := by
  rcases d with ⟨v, side⟩
  rw [fkMedialLocalMate_eq_localSideMate]
  unfold fkColoredStrandSpliceRawColor
  rw [fkColoredSideSlot_localMate]

def FKColoredStrandSpliceBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (fkLayeredBondMate T x) =
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv x





theorem fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) :
    FKColoredStrandSpliceBondCoherent source targetPairing slotEquiv ↔
      forall x : FKLayeredMedialDart T,
        fkColoredStrandSpliceRawColor source targetPairing slotEquiv
            (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
          fkColoredStrandSpliceRawColor source targetPairing slotEquiv x := by
  constructor
  · intro hbond x
    rw [fkMedialBoundaryStep_apply]
    exact (hbond
      (x.1, fkMedialLocalMate (targetPairing x.1) x.2)).trans
        (fkColoredStrandSpliceRawColor_localMate
          source targetPairing slotEquiv x.1 x.2)
  · intro hboundary x
    let dlocal := fkMedialLocalMate (targetPairing x.1) x.2
    have h := hboundary (x.1, dlocal)
    rw [fkMedialBoundaryStep_apply,
      fkMedialLocalMate_involutive] at h
    exact h.trans
      (fkColoredStrandSpliceRawColor_localMate
        source targetPairing slotEquiv x.1 x.2)

structure FKColoredStrandSplice
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  targetPairing : Bool -> FKMedialLoopPairing T
  slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T
  bondCoherent : FKColoredStrandSpliceBondCoherent
    source targetPairing slotEquiv



def FKColoredStrandSplice.ofBoundaryInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hboundary : forall x : FKLayeredMedialDart T,
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv
          (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
        fkColoredStrandSpliceRawColor source targetPairing slotEquiv x) :
    FKColoredStrandSplice source where
  targetPairing := targetPairing
  slotEquiv := slotEquiv
  bondCoherent :=
    (fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant
      source targetPairing slotEquiv).2 hboundary

def FKColoredStrandSlotColorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Prop :=
  forall slot,
    fkColoredLayeredSlotColor source (slotEquiv slot) =
      fkColoredLayeredSlotColor target slot

def fkColoredTrueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) : Nat :=
  Fintype.card {slot : FKLayeredStrandSlot T //
    fkColoredLayeredSlotColor source slot = true}

noncomputable def boolFalseFiberEquivComplementTrue
    {A : Type*} [Fintype A] (color : A -> Bool) :
    {x : A // color x = false} ≃ {x : A // ¬ color x = true} :=
  Equiv.subtypeEquiv (Equiv.refl A) fun x => by
    generalize hcolor : color x = value
    cases value <;> simp [hcolor]

theorem card_boolFalseFiber
    {A : Type*} [Fintype A] (color : A -> Bool) :
    Fintype.card {x : A // color x = false} =
      Fintype.card A - Fintype.card {x : A // color x = true} := by
  rw [Fintype.card_congr (boolFalseFiberEquivComplementTrue color)]
  exact Fintype.card_subtype_compl (fun x => color x = true)



noncomputable def fkColoredStrandSlotEquivOfFiberCards
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (hcard : forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color}) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  Equiv.ofFiberEquiv fun color =>
    Fintype.equivOfCardEq (hcard color)

theorem fkColoredStrandSlotEquivOfFiberCards_color
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (hcard : forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color}) :
    FKColoredStrandSlotColorEquiv source target
      (fkColoredStrandSlotEquivOfFiberCards source target hcard) := by
  intro slot
  rw [fkColoredStrandSlotEquivOfFiberCards,
    Equiv.ofFiberEquiv_apply]
  exact (Fintype.equivOfCardEq
    (hcard (fkColoredLayeredSlotColor target slot))
    ((Equiv.sigmaFiberEquiv
      (fkColoredLayeredSlotColor target)).symm slot).snd).2

theorem fkColoredStrandSlotFiberCards_of_trueCount_eq
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color} := by
  intro color
  cases color
  · rw [card_boolFalseFiber, card_boolFalseFiber]
    unfold fkColoredTrueStrandSlotCount at htrue
    rw [← htrue]
  · exact htrue.symm

noncomputable def fkColoredStrandSlotEquivOfTrueCount
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  fkColoredStrandSlotEquivOfFiberCards source target
    (fkColoredStrandSlotFiberCards_of_trueCount_eq source target htrue)

theorem fkColoredStrandSlotEquivOfTrueCount_color
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    FKColoredStrandSlotColorEquiv source target
      (fkColoredStrandSlotEquivOfTrueCount source target htrue) :=
  fkColoredStrandSlotEquivOfFiberCards_color source target _

theorem fkColoredStrandSpliceRawColor_eq_of_colorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv)
    (x : FKLayeredMedialDart T) :
    fkColoredStrandSpliceRawColor source
        (fun layer => (target layer).pairing) slotEquiv x =
      (target x.1).color x.2 := by
  rcases x with ⟨layer, v, side⟩
  unfold fkColoredStrandSpliceRawColor
  rw [hcolor]
  exact (FKColoredLoopPairing.color_eq_slotColor
    target layer v side).symm



def FKColoredStrandSplice.ofColorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
    FKColoredStrandSplice source where
  targetPairing := fun layer => (target layer).pairing
  slotEquiv := slotEquiv
  bondCoherent := by
    intro x
    rw [fkColoredStrandSpliceRawColor_eq_of_colorEquiv
        source target slotEquiv hcolor,
      fkColoredStrandSpliceRawColor_eq_of_colorEquiv
        source target slotEquiv hcolor]
    rcases x with ⟨layer, d⟩
    exact (target layer).color_bondMate d

def FKColoredStrandSplice.target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := splice.targetPairing layer
    color := fun d => fkColoredStrandSpliceRawColor source
      splice.targetPairing splice.slotEquiv (layer, d)
    color_localMate := fkColoredStrandSpliceRawColor_localMate
      source splice.targetPairing splice.slotEquiv layer
    color_bondMate := by
      intro d
      exact splice.bondCoherent (layer, d) }

@[simp] theorem FKColoredStrandSplice.ofColorEquiv_target
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
    (FKColoredStrandSplice.ofColorEquiv
      source target slotEquiv hcolor).target = target := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact fkColoredStrandSpliceRawColor_eq_of_colorEquiv
      source target slotEquiv hcolor (layer, d)

theorem FKColoredStrandSplice.target_slotColor
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor splice.target slot =
      fkColoredLayeredSlotColor source (splice.slotEquiv slot) := by
  rcases slot with ⟨layer, v, slot⟩
  cases slot <;>
    simp [fkColoredLayeredSlotColor, FKColoredStrandSplice.target,
      fkColoredStrandSpliceRawColor]



theorem FKColoredStrandSplice.target_trueStrandSlotCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    fkColoredTrueStrandSlotCount splice.target =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv splice.slotEquiv
  intro slot
  rw [splice.target_slotColor]

theorem FKColoredStrandSplice.symm_rawColor
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (x : FKLayeredMedialDart T) :
    fkColoredStrandSpliceRawColor splice.target
        (fun layer => (source layer).pairing) splice.slotEquiv.symm x =
      (source x.1).color x.2 := by
  rcases x with ⟨layer, v, side⟩
  unfold fkColoredStrandSpliceRawColor
  rw [splice.target_slotColor]
  rw [splice.slotEquiv.apply_symm_apply]
  exact (FKColoredLoopPairing.color_eq_slotColor
    source layer v side).symm

theorem FKColoredStrandSplice.symm_bondCoherent
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    FKColoredStrandSpliceBondCoherent splice.target
      (fun layer => (source layer).pairing) splice.slotEquiv.symm := by
  intro x
  rw [splice.symm_rawColor, splice.symm_rawColor]
  rcases x with ⟨layer, d⟩
  exact (source layer).color_bondMate d


def FKColoredStrandSplice.symm
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    FKColoredStrandSplice splice.target where
  targetPairing := fun layer => (source layer).pairing
  slotEquiv := splice.slotEquiv.symm
  bondCoherent := splice.symm_bondCoherent

@[simp] theorem FKColoredStrandSplice.symm_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    splice.symm.target = source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact splice.symm_rawColor (layer, d)

def fkColoredSlotPairEqualCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Nat :=
  ∑ v : T.Vertex, (
    (if fkColoredLayeredSlotColor source (slotEquiv (false, v, false)) =
        fkColoredLayeredSlotColor source (slotEquiv (false, v, true))
      then 1 else 0) +
    (if fkColoredLayeredSlotColor source (slotEquiv (true, v, false)) =
        fkColoredLayeredSlotColor source (slotEquiv (true, v, true))
      then 1 else 0))

theorem fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairTotalC source =
      fkColoredSlotPairEqualCount source (Equiv.refl _) := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
    fkColoredSlotPairEqualCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hfalse : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases htrue : (source true).color (v, .west) =
      (source true).color (v, .east) <;>
    simp [fkColoredLayeredSlotColor, hfalse, htrue]

theorem FKColoredStrandSplice.target_totalC_eq_slotPairEqualCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    fkColoredLoopPairingPairTotalC splice.target =
      fkColoredSlotPairEqualCount source splice.slotEquiv := by
  rw [fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]
  unfold fkColoredSlotPairEqualCount
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Equiv.refl_apply]
  simp only [splice.target_slotColor]

def FKColoredStrandSplice.PreservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) : Prop :=
  fkColoredSlotPairEqualCount source splice.slotEquiv =
    fkColoredSlotPairEqualCount source (Equiv.refl _)

theorem FKColoredStrandSplice.target_totalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (hC : splice.PreservesTotalC) :
    fkColoredLoopPairingPairTotalC splice.target =
      fkColoredLoopPairingPairTotalC source := by
  rw [splice.target_totalC_eq_slotPairEqualCount, hC,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]

def FKColoredStrandSplice.seamDelta
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) (layer : Bool) : Int :=
  ∑ i : Fin T.width, (
    ((splice.target layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat -
      ((source layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat : Int)

theorem FKColoredStrandSplice.target_upCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) (layer : Bool) :
    (sixVertexUpCount
        (svTorusVerticalRows T (splice.target layer).arrows
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T (source layer).arrows
          (svFinLast T.height_pos)) : Int) + splice.seamDelta layer := by
  let targetRow := svTorusVerticalRows T (splice.target layer).arrows
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T (source layer).arrows
    (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  unfold FKColoredStrandSplice.seamDelta
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring

theorem FKColoredStrandSplice.target_middleSectors
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (n : Nat) (hn : 0 < n)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = n - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = n + 1)
    (hdeltaLower : splice.seamDelta false = 1)
    (hdeltaUpper : splice.seamDelta true = -1) :
    sixVertexUpCount
        (svTorusVerticalRows T (splice.target false).arrows
          (svFinLast T.height_pos)) = n /\
      sixVertexUpCount
        (svTorusVerticalRows T (splice.target true).arrows
          (svFinLast T.height_pos)) = n := by
  constructor
  · have h := splice.target_upCount false
    rw [hlower, hdeltaLower] at h
    have hnInt : ((n - 1 : Nat) : Int) + 1 = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h
  · have h := splice.target_upCount true
    rw [hupper, hdeltaUpper] at h
    have hnInt : ((n + 1 : Nat) : Int) + (-1) = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h

end

end StatMech.FrontierD
