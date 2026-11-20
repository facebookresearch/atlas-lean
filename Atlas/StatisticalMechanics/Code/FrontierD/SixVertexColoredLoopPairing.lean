/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairLoopFiber
import Code.FrontierD.FKMedialBoundaryToggleParity










namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropColoredLoopPairing (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem boolXor_eq_of_ne_ne
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    (a ^^ c) = (b ^^ d) := by
  decide +revert

theorem sixVertexIsCType_iff_horizontalIncoming_eq
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    omega.IsCType v ↔
      fkLoopWestIncoming omega v = fkLoopEastIncoming omega v := by
  unfold SixVertexArrows.IsCType fkLoopWestIncoming fkLoopEastIncoming
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  cases w <;> cases e <;> simp



structure FKColoredLoopPairing (T : EvenTorus) where
  pairing : FKMedialLoopPairing T
  color : FKMedialDart T → Bool
  color_localMate : ∀ d, color (fkMedialLocalMate pairing d) = color d
  color_bondMate : ∀ d, color (fkMedialBondMate T d) = color d

@[ext] theorem FKColoredLoopPairing.ext
    {T : EvenTorus} {a b : FKColoredLoopPairing T}
    (hpairing : a.pairing = b.pairing) (hcolor : a.color = b.color) :
    a = b := by
  cases a
  cases b
  simp_all

def FKColoredLoopPairing.incoming
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) : Bool :=
  fkMedialCheckerColor d ^^ colored.color d

def FKColoredLoopPairing.arrows
    {T : EvenTorus} (colored : FKColoredLoopPairing T) : SixVertexArrows T where
  horizontal v := !colored.incoming (v, .east)
  vertical v := !colored.incoming (v, .north)

theorem FKColoredLoopPairing.incoming_bondMate
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    (!colored.incoming (fkMedialBondMate T d)) = colored.incoming d := by
  have hcolor := fkMedialCheckerColor_bondMate_ne T d
  unfold incoming
  rw [show colored.color (fkMedialBondMate T d) = colored.color d by
    exact colored.color_bondMate d]
  generalize hc : fkMedialCheckerColor d = c at hcolor ⊢
  generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hcolor ⊢
  generalize hm : colored.color d = m
  cases c <;> cases b <;> cases m <;> simp_all

theorem FKColoredLoopPairing.incoming_localMate_ne
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    colored.incoming (fkMedialLocalMate colored.pairing d) ≠
      colored.incoming d := by
  have hcolor := fkMedialCheckerColor_localMate_ne colored.pairing d
  unfold incoming
  rw [show colored.color (fkMedialLocalMate colored.pairing d) =
      colored.color d by exact colored.color_localMate d]
  generalize hc : fkMedialCheckerColor d = c at hcolor ⊢
  generalize hm : fkMedialCheckerColor
    (fkMedialLocalMate colored.pairing d) = m at hcolor ⊢
  generalize hb : colored.color d = b
  cases c <;> cases m <;> cases b <;> simp_all

theorem FKColoredLoopPairing.dartIncoming_arrows
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialDartIncoming colored.arrows d = colored.incoming d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp only [fkMedialDartIncoming, fkLoopWestIncoming, arrows]
    exact colored.incoming_bondMate ((i, j), .west)
  · simp [fkMedialDartIncoming, fkLoopEastIncoming, arrows]
  · simp only [fkMedialDartIncoming, fkLoopSouthIncoming, arrows]
    exact colored.incoming_bondMate ((i, j), .south)
  · simp [fkMedialDartIncoming, fkLoopNorthIncoming, arrows]

theorem FKColoredLoopPairing.compatible
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    ∀ v, fkLoopPairingCompatible (colored.pairing v)
      colored.arrows v := by
  intro v
  cases hp : colored.pairing v
  · constructor
    · change fkMedialDartIncoming colored.arrows (v, .west) ≠
        fkMedialDartIncoming colored.arrows (v, .north)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .west)).symm
    · change fkMedialDartIncoming colored.arrows (v, .east) ≠
        fkMedialDartIncoming colored.arrows (v, .south)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .east)).symm
  · constructor
    · change fkMedialDartIncoming colored.arrows (v, .west) ≠
        fkMedialDartIncoming colored.arrows (v, .south)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .west)).symm
    · change fkMedialDartIncoming colored.arrows (v, .east) ≠
        fkMedialDartIncoming colored.arrows (v, .north)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .east)).symm

theorem FKColoredLoopPairing.iceRule
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    colored.arrows.IceRule := by
  intro v
  exact incomingCount_eq_two_of_fkLoopPairingCompatible
    (colored.pairing v) colored.arrows v (colored.compatible v)

theorem FKColoredLoopPairing.cType_iff_color_west_eq_east
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex) :
    colored.arrows.IsCType v ↔
      colored.color (v, .west) = colored.color (v, .east) := by
  rw [sixVertexIsCType_iff_horizontalIncoming_eq]
  rw [show fkLoopWestIncoming colored.arrows v =
      colored.incoming (v, .west) by
    exact colored.dartIncoming_arrows (v, .west),
    show fkLoopEastIncoming colored.arrows v =
      colored.incoming (v, .east) by
    exact colored.dartIncoming_arrows (v, .east)]
  unfold incoming
  have hc : fkMedialCheckerColor (v, FKMedialSide.west) =
      fkMedialCheckerColor (v, FKMedialSide.east) := rfl
  generalize hw : colored.color (v, FKMedialSide.west) = w
  generalize he : colored.color (v, FKMedialSide.east) = e
  generalize hcw : fkMedialCheckerColor (v, FKMedialSide.west) = cw at hc ⊢
  generalize hce : fkMedialCheckerColor (v, FKMedialSide.east) = ce at hc ⊢
  cases w <;> cases e <;> cases cw <;> cases ce <;> simp_all


abbrev FKColoredLoopPairingPair (T : EvenTorus) :=
  Bool → FKColoredLoopPairing T


def SixVertexCompatibleLoopPairing.toColored
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    FKColoredLoopPairing T where
  pairing := pairing.1
  color d := fkMedialCheckerColor d ^^ fkMedialDartIncoming omega d
  color_localMate := by
    intro d
    have hc := fkMedialCheckerColor_localMate_ne pairing.1 d
    have hi := fkMedialDartIncoming_localMate_ne pairing.1 omega pairing.2 d
    generalize hca : fkMedialCheckerColor
      (fkMedialLocalMate pairing.1 d) = ca at hc ⊢
    generalize hcb : fkMedialCheckerColor d = cb at hc ⊢
    generalize hia : fkMedialDartIncoming omega
      (fkMedialLocalMate pairing.1 d) = ia at hi ⊢
    generalize hib : fkMedialDartIncoming omega d = ib at hi ⊢
    exact boolXor_eq_of_ne_ne hc hi
  color_bondMate := by
    intro d
    have hc := fkMedialCheckerColor_bondMate_ne T d
    have hi := fkMedialDartIncoming_bondMate_ne T omega d
    generalize hca : fkMedialCheckerColor (fkMedialBondMate T d) = ca at hc ⊢
    generalize hcb : fkMedialCheckerColor d = cb at hc ⊢
    generalize hia : fkMedialDartIncoming omega
      (fkMedialBondMate T d) = ia at hi ⊢
    generalize hib : fkMedialDartIncoming omega d = ib at hi ⊢
    exact boolXor_eq_of_ne_ne hc hi

theorem SixVertexCompatibleLoopPairing.toColored_incoming
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega)
    (d : FKMedialDart T) :
    pairing.toColored.incoming d = fkMedialDartIncoming omega d := by
  change (fkMedialCheckerColor d ^^
      (fkMedialCheckerColor d ^^ fkMedialDartIncoming omega d)) =
    fkMedialDartIncoming omega d
  generalize hc : fkMedialCheckerColor d = c
  generalize hi : fkMedialDartIncoming omega d = i
  cases c <;> cases i <;> rfl

@[simp] theorem SixVertexCompatibleLoopPairing.toColored_arrows
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    pairing.toColored.arrows = omega := by
  ext v
  · change (!pairing.toColored.incoming (v, .east)) = omega.horizontal v
    rw [pairing.toColored_incoming]
    simp [fkMedialDartIncoming, fkLoopEastIncoming]
  · change (!pairing.toColored.incoming (v, .north)) = omega.vertical v
    rw [pairing.toColored_incoming]
    simp [fkMedialDartIncoming, fkLoopNorthIncoming]


def FKColoredLoopPairing.toCompatible
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    SixVertexCompatibleLoopPairing colored.arrows :=
  ⟨colored.pairing, colored.compatible⟩

@[simp] theorem FKColoredLoopPairing.toCompatible_toColored
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    colored.toCompatible.toColored = colored := by
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    change (fkMedialCheckerColor d ^^
        fkMedialDartIncoming colored.arrows d) = colored.color d
    rw [colored.dartIncoming_arrows]
    change (fkMedialCheckerColor d ^^
        (fkMedialCheckerColor d ^^ colored.color d)) = colored.color d
    generalize hc : fkMedialCheckerColor d = c
    generalize hm : colored.color d = m
    cases c <;> cases m <;> rfl


structure FKColoredLocalPairing where
  pairing : Bool
  west : Bool
  east : Bool
deriving DecidableEq

@[ext] theorem FKColoredLocalPairing.ext
    {a b : FKColoredLocalPairing}
    (hpairing : a.pairing = b.pairing)
    (hwest : a.west = b.west) (heast : a.east = b.east) : a = b := by
  cases a
  cases b
  simp_all

def FKColoredLocalPairing.sideColor
    (cfg : FKColoredLocalPairing) (side : FKMedialSide) : Bool :=
  match cfg.pairing, side with
  | false, .west => cfg.west
  | false, .north => cfg.west
  | false, .east => cfg.east
  | false, .south => cfg.east
  | true, .west => cfg.west
  | true, .south => cfg.west
  | true, .east => cfg.east
  | true, .north => cfg.east

@[simp] theorem FKColoredLocalPairing.sideColor_west
    (cfg : FKColoredLocalPairing) : cfg.sideColor .west = cfg.west := by
  rcases cfg with ⟨pairing, west, east⟩
  cases pairing <;> rfl

@[simp] theorem FKColoredLocalPairing.sideColor_east
    (cfg : FKColoredLocalPairing) : cfg.sideColor .east = cfg.east := by
  rcases cfg with ⟨pairing, west, east⟩
  cases pairing <;> rfl

def fkMedialLocalSideMate
    (pairing : Bool) (side : FKMedialSide) : FKMedialSide :=
  match pairing, side with
  | false, .west => .north
  | false, .north => .west
  | false, .east => .south
  | false, .south => .east
  | true, .west => .south
  | true, .south => .west
  | true, .east => .north
  | true, .north => .east

theorem fkMedialLocalMate_eq_localSideMate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (side : FKMedialSide) :
    fkMedialLocalMate pairing (v, side) =
      (v, fkMedialLocalSideMate (pairing v) side) := by
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialLocalSideMate, hp]

theorem FKColoredLocalPairing.sideColor_localMate
    (cfg : FKColoredLocalPairing) (side : FKMedialSide) :
    cfg.sideColor (fkMedialLocalSideMate cfg.pairing side) =
      cfg.sideColor side := by
  cases cfg with
  | mk pairing west east =>
    cases pairing <;> cases side <;> rfl

def FKColoredLoopPairing.localPairing
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex) :
    FKColoredLocalPairing where
  pairing := colored.pairing v
  west := colored.color (v, .west)
  east := colored.color (v, .east)

theorem FKColoredLoopPairing.localPairing_sideColor
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex)
    (side : FKMedialSide) :
    (colored.localPairing v).sideColor side = colored.color (v, side) := by
  cases hp : colored.pairing v
  · cases side
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .east)).symm
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .west)).symm
  · cases side
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .west)).symm
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .east)).symm


def fkColoredLocalPairCross
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.1.west, east := pair.2.east },
   { pairing := pair.2.pairing, west := pair.2.west, east := pair.1.east })


def fkColoredLocalPairCrossWest
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.2.west, east := pair.1.east },
   { pairing := pair.2.pairing, west := pair.1.west, east := pair.2.east })


def fkColoredLocalPairReconnection
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.2.west, east := pair.2.east },
   { pairing := pair.2.pairing, west := pair.1.west, east := pair.1.east })



def fkColoredLocalPairOddCross
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  if pair.1.west != pair.2.west then fkColoredLocalPairCrossWest pair
  else fkColoredLocalPairCross pair

@[simp] theorem fkColoredLocalPairCross_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCross (fkColoredLocalPairCross pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

@[simp] theorem fkColoredLocalPairCrossWest_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCrossWest (fkColoredLocalPairCrossWest pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

@[simp] theorem fkColoredLocalPairOddCross_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairOddCross (fkColoredLocalPairOddCross pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  cases a <;> cases c <;> rfl

@[simp] theorem fkColoredLocalPairReconnection_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairReconnection
        (fkColoredLocalPairReconnection pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

def fkColoredLocalPairCTypeCount
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) : Nat :=
  (if pair.1.west = pair.1.east then 1 else 0) +
    (if pair.2.west = pair.2.east then 1 else 0)

theorem fkColoredLocalPairOddCross_cTypeCount_of_odd
    (pair : FKColoredLocalPairing × FKColoredLocalPairing)
    (hodd : pair.1.west ^^ pair.1.east ^^
      pair.2.west ^^ pair.2.east = true) :
    fkColoredLocalPairCTypeCount (fkColoredLocalPairOddCross pair) =
      fkColoredLocalPairCTypeCount pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [fkColoredLocalPairCTypeCount, fkColoredLocalPairOddCross,
      fkColoredLocalPairCross, fkColoredLocalPairCrossWest] at hodd ⊢

@[simp] theorem fkColoredLocalPairReconnection_cTypeCount
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCTypeCount (fkColoredLocalPairReconnection pair) =
      fkColoredLocalPairCTypeCount pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  by_cases hab : a = b <;> by_cases hcd : c = d <;>
    simp [fkColoredLocalPairCTypeCount, fkColoredLocalPairReconnection,
      add_comm, hab, hcd]

theorem FKColoredLoopPairingPair.localCTypeCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (v : T.Vertex) :
    fkColoredLocalPairCTypeCount
        ((source false).localPairing v, (source true).localPairing v) =
      (if (source false).arrows.IsCType v then 1 else 0) +
        (if (source true).arrows.IsCType v then 1 else 0) := by
  unfold fkColoredLocalPairCTypeCount FKColoredLoopPairing.localPairing
  change (if (source false).color (v, .west) =
        (source false).color (v, .east) then 1 else 0) +
      (if (source true).color (v, .west) =
        (source true).color (v, .east) then 1 else 0) = _
  rw [(source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hfalse : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases htrue : (source true).color (v, .west) =
      (source true).color (v, .east) <;> simp [hfalse, htrue]

def fkColoredLocalPairCrossIf
    (cross : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  if cross then fkColoredLocalPairReconnection pair else pair

@[simp] theorem fkColoredLocalPairCrossIf_involutive
    (cross : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCrossIf cross
        (fkColoredLocalPairCrossIf cross pair) = pair := by
  cases cross <;> simp [fkColoredLocalPairCrossIf]

theorem fkColoredLocalPairCrossIf_pairing
    (cross layer : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    (if layer then (fkColoredLocalPairCrossIf cross pair).2.pairing
      else (fkColoredLocalPairCrossIf cross pair).1.pairing) =
    (if layer then pair.2.pairing else pair.1.pairing) := by
  cases cross <;> cases layer <;>
    simp [fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection]

abbrev FKLayeredMedialDart (T : EvenTorus) :=
  Bool × FKMedialDart T

def fkLayeredLoopColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (x : FKLayeredMedialDart T) : Bool :=
  (source x.1).color x.2

def fkLayeredBondMate
    (T : EvenTorus) (x : FKLayeredMedialDart T) :
    FKLayeredMedialDart T :=
  (x.1, fkMedialBondMate T x.2)


def fkColoredVertexCrossRawColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) (x : FKLayeredMedialDart T) : Bool :=
  let localPair :=
    ((source false).localPairing x.2.1,
      (source true).localPairing x.2.1)
  let crossed := fkColoredLocalPairCrossIf (mask x.2.1) localPair
  (if x.1 then crossed.2 else crossed.1).sideColor x.2.2

theorem fkColoredVertexCrossRawColor_localMate
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) (layer : Bool) (d : FKMedialDart T) :
    fkColoredVertexCrossRawColor source mask
        (layer, fkMedialLocalMate (source layer).pairing d) =
      fkColoredVertexCrossRawColor source mask (layer, d) := by
  rcases d with ⟨v, side⟩
  let pair := ((source false).localPairing v,
    (source true).localPairing v)
  let crossed := fkColoredLocalPairCrossIf (mask v) pair
  let cfg := if layer then crossed.2 else crossed.1
  have hp : cfg.pairing = (source layer).pairing v := by
    cases layer
    · simpa [cfg, crossed, pair] using
        (fkColoredLocalPairCrossIf_pairing (mask v) false pair)
    · simpa [cfg, crossed, pair] using
        (fkColoredLocalPairCrossIf_pairing (mask v) true pair)
  rw [fkMedialLocalMate_eq_localSideMate]
  change cfg.sideColor
      (fkMedialLocalSideMate ((source layer).pairing v) side) =
    cfg.sideColor side
  rw [← hp]
  exact cfg.sideColor_localMate side



def FKColoredVertexCrossBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredVertexCrossRawColor source mask (fkLayeredBondMate T x) =
      fkColoredVertexCrossRawColor source mask x



def fkColoredVertexCrossTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := (source layer).pairing
    color := fun d => fkColoredVertexCrossRawColor source mask (layer, d)
    color_localMate := fkColoredVertexCrossRawColor_localMate source mask layer
    color_bondMate := by
      intro d
      exact hbond (layer, d) }

theorem fkColoredVertexCrossTarget_localPairing
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (v : T.Vertex) :
    ((fkColoredVertexCrossTarget source mask hbond false).localPairing v,
        (fkColoredVertexCrossTarget source mask hbond true).localPairing v) =
      fkColoredLocalPairCrossIf (mask v)
        ((source false).localPairing v, (source true).localPairing v) := by
  cases hm : mask v <;>
    by_cases hwest : (source false).color (v, .west) =
      (source true).color (v, .west)
  all_goals apply Prod.ext
  all_goals apply FKColoredLocalPairing.ext
  all_goals simp [fkColoredVertexCrossTarget,
    FKColoredLoopPairing.localPairing, fkColoredVertexCrossRawColor,
    fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection,
    hm, hwest]

theorem fkColoredVertexCrossRawColor_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (x : FKLayeredMedialDart T) :
    fkColoredVertexCrossRawColor
        (fkColoredVertexCrossTarget source mask hbond) mask x =
      fkLayeredLoopColor source x := by
  rcases x with ⟨layer, ⟨v, side⟩⟩
  unfold fkColoredVertexCrossRawColor
  rw [fkColoredVertexCrossTarget_localPairing]
  let pair := ((source false).localPairing v,
    (source true).localPairing v)
  change (if layer then
      (fkColoredLocalPairCrossIf (mask v)
        (fkColoredLocalPairCrossIf (mask v) pair)).2
    else
      (fkColoredLocalPairCrossIf (mask v)
        (fkColoredLocalPairCrossIf (mask v) pair)).1).sideColor side = _
  rw [fkColoredLocalPairCrossIf_involutive]
  unfold fkLayeredLoopColor
  cases layer
  · exact (source false).localPairing_sideColor v side
  · exact (source true).localPairing_sideColor v side

theorem fkColoredVertexCrossTarget_bondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    FKColoredVertexCrossBondCoherent
      (fkColoredVertexCrossTarget source mask hbond) mask := by
  intro x
  rw [fkColoredVertexCrossRawColor_target,
    fkColoredVertexCrossRawColor_target]
  rcases x with ⟨layer, d⟩
  exact (source layer).color_bondMate d



@[simp] theorem fkColoredVertexCrossTarget_involutive
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredVertexCrossTarget
        (fkColoredVertexCrossTarget source mask hbond) mask
        (fkColoredVertexCrossTarget_bondCoherent source mask hbond) =
      source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact fkColoredVertexCrossRawColor_target source mask hbond (layer, d)

def fkColoredLoopPairingPairTotalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) : Nat :=
  sixVertexTorusCTypeCount (source false).arrows +
    sixVertexTorusCTypeCount (source true).arrows

theorem fkColoredVertexCrossTarget_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredLoopPairingPairTotalC
        (fkColoredVertexCrossTarget source mask hbond) =
      fkColoredLoopPairingPairTotalC source := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← FKColoredLoopPairingPair.localCTypeCount,
    ← FKColoredLoopPairingPair.localCTypeCount,
    fkColoredVertexCrossTarget_localPairing]
  cases hm : mask v
  · rfl
  · exact fkColoredLocalPairReconnection_cTypeCount _

def fkColoredVertexCrossSeamDelta
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (layer : Bool) : Int :=
  ∑ i : Fin T.width, (
    ((fkColoredVertexCrossTarget source mask hbond layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat -
      ((source layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat : Int)

theorem fkColoredVertexCrossTarget_upCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (layer : Bool) :
    (sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond layer).arrows
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T (source layer).arrows
          (svFinLast T.height_pos)) : Int) +
        fkColoredVertexCrossSeamDelta source mask hbond layer := by
  let targetRow := svTorusVerticalRows T
    (fkColoredVertexCrossTarget source mask hbond layer).arrows
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T (source layer).arrows
    (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  unfold fkColoredVertexCrossSeamDelta
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring

theorem fkColoredVertexCrossTarget_middleSectors
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (n : Nat) (hn : 0 < n)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = n - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = n + 1)
    (hdeltaLower : fkColoredVertexCrossSeamDelta
      source mask hbond false = 1)
    (hdeltaUpper : fkColoredVertexCrossSeamDelta
      source mask hbond true = -1) :
    sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond false).arrows
          (svFinLast T.height_pos)) = n /\
      sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond true).arrows
          (svFinLast T.height_pos)) = n := by
  constructor
  · have h := fkColoredVertexCrossTarget_upCount
      source mask hbond false
    rw [hlower, hdeltaLower] at h
    have hnInt : ((n - 1 : Nat) : Int) + 1 = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h
  · have h := fkColoredVertexCrossTarget_upCount
      source mask hbond true
    rw [hupper, hdeltaUpper] at h
    have hnInt : ((n + 1 : Nat) : Int) + (-1) = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h

end

end StatMech.FrontierD
