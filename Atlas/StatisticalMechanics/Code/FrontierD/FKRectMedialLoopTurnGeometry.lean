/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.FKRectRefinedEdgeCenterClass
import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.FrontierD.FKMedialLoopTurnWalk

namespace StatMech.FrontierD
noncomputable section

theorem fkRectClosedPairing_eq_not_vertexParity
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) =
      !fkMedialVertexParity v := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = (fkRectTorusMedialEdgeEquiv R).symm e := by
    simp [e]
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectClosedPairingAtEdge, fkMedialVertexParity, hy,
      Bool.toNat]

def fkRectBlackDartSite (R : FKRectTorus)
    (d : FKMedialBlackDart R.medialTorus) :=
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  fkRectIntegralSquarePointMod L
    (fkRectRefinedDartPoint
      (fkRectRefinedBoundaryCanonicalCenter R d.1) d.1.2)



def fkRectBlackDartShiftedPoint (R : FKRectTorus)
    (u : Int × Int) (d : FKMedialBlackDart R.medialTorus) :=
  let A := fkRectSquareDeckTranslation R u
  let c := fkRectRefinedBoundaryCanonicalCenter R d.1
  fkRectRefinedDartPoint
    (c.1 + 4 * A.1, c.2 + 4 * A.2) d.1.2


def fkRectBlackDartShiftedSite (R : FKRectTorus)
    (u : Int × Int) (d : FKMedialBlackDart R.medialTorus) :=
  fkRectIntegralSquarePointMod
    (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))
    (fkRectBlackDartShiftedPoint R u d)

@[simp] theorem fkRectBlackDartShiftedSite_zero
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackDartShiftedSite R (0, 0) d =
      fkRectBlackDartSite R d := by
  simp [fkRectBlackDartShiftedSite, fkRectBlackDartSite,
    fkRectBlackDartShiftedPoint, fkRectSquareDeckTranslation]

def fkRectRefinedDartResidue (horizontal : Bool)
    (side : FKMedialSide) : ZMod 4 × ZMod 4 :=
  match horizontal, side with
  | true, .west => (1, 3)
  | true, .east => (3, 1)
  | true, .south => (1, 1)
  | true, .north => (3, 3)
  | false, .west => (3, 1)
  | false, .east => (1, 3)
  | false, .south => (3, 3)
  | false, .north => (1, 1)

theorem fkRectRefinedDartSite_reduce_four {L : Nat} (h4 : 4 ∣ L)
    (horizontal : Bool) (c : Int × Int) (side : FKMedialSide)
    (hc : FKRectRefinedEdgeCenterNormal horizontal c) :
    (ZMod.castHom h4 (ZMod 4)
        (fkRectIntegralSquarePointMod L
          (fkRectRefinedDartPoint c side)).1,
      ZMod.castHom h4 (ZMod 4)
        (fkRectIntegralSquarePointMod L
          (fkRectRefinedDartPoint c side)).2) =
      fkRectRefinedDartResidue horizontal side := by
  have hcast (z : Int) :
      ZMod.castHom h4 (ZMod 4) (z : ZMod L) = (z : ZMod 4) := by
    rw [ZMod.castHom_apply]
    exact ZMod.cast_intCast h4 z
  have hfour : (4 : ZMod 4) = 0 := by decide
  have hmone : (-1 : ZMod 4) = 3 := by decide
  have hmthree : (-3 : ZMod 4) = 1 := by decide
  have htwoThree : (2 + 3 : ZMod 4) = 1 := by decide
  have htwoOne : (2 + 1 : ZMod 4) = 3 := by decide
  have hmTwoThree : (-2 + 3 : ZMod 4) = 1 := by decide
  have hmTwoOne : (-2 + 1 : ZMod 4) = 3 := by decide
  cases horizontal
  · simp only [FKRectRefinedEdgeCenterNormal, if_false] at hc
    obtain ⟨x, y, rfl⟩ := hc
    cases side <;> ext <;>
      simp only [fkRectIntegralSquarePointMod, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectRefinedDartResidue,
        Prod.fst, Prod.snd]
    all_goals
      change ZMod.castHom h4 (ZMod 4) ((_: Int) : ZMod L) = _
      rw [hcast]
      push_cast
      simp [hfour, hmone, hmthree, htwoThree, htwoOne,
        hmTwoThree, hmTwoOne]
  · simp only [FKRectRefinedEdgeCenterNormal, if_true] at hc
    obtain ⟨x, y, rfl⟩ := hc
    cases side <;> ext <;>
      simp only [fkRectIntegralSquarePointMod, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectRefinedDartResidue,
        Prod.fst, Prod.snd]
    all_goals
      change ZMod.castHom h4 (ZMod 4) ((_: Int) : ZMod L) = _
      rw [hcast]
      push_cast
      simp [hfour, hmone, hmthree, htwoThree, htwoOne,
        hmTwoThree, hmTwoOne]

theorem fkRectRefinedDartResidue_injective_of_blackSide
    (p q : Bool) (s t : FKMedialSide)
    (hs : fkMedialSideVertical s = !p)
    (ht : fkMedialSideVertical t = !q)
    (h : fkRectRefinedDartResidue p s =
      fkRectRefinedDartResidue q t) :
    p = q ∧ s = t := by
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  have h13 : (1 : ZMod 4) ≠ 3 := h31.symm
  cases p <;> cases q <;> cases s <;> cases t <;>
    simp [fkMedialSideVertical, fkRectRefinedDartResidue,
      h31, h13] at hs ht h ⊢

theorem fkRectBlackDart_sideVertical (R : FKRectTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    fkMedialSideVertical d.1.2 =
      !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1.1) := by
  have hp := fkRectClosedPairing_eq_not_vertexParity R d.1.1
  have hd := d.2
  unfold fkMedialCheckerColor at hd
  generalize hpair :
      fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1.1) = p at hp ⊢
  generalize hpar : fkMedialVertexParity d.1.1 = v at hp hd
  generalize hside : fkMedialSideVertical d.1.2 = s at hd ⊢
  cases p <;> cases v <;> cases s <;> simp at hp hd ⊢

theorem fkRectBlackDartSite_injective (R : FKRectTorus) :
    Function.Injective (fkRectBlackDartSite R) := by
  classical
  intro d e hsite
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have h4 : 4 ∣ L := by
    refine ⟨fkRectSquareCoverSide R, ?_⟩
    simp [L]
  let pd := fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1.1)
  let pe := fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R e.1.1)
  have hnormald := fkRectRefinedBoundaryCanonicalCenter_normal R d.1
  have hnormale := fkRectRefinedBoundaryCanonicalCenter_normal R e.1
  have hreduce := congrArg (fun z : ZMod L × ZMod L =>
    (ZMod.castHom h4 (ZMod 4) z.1,
      ZMod.castHom h4 (ZMod 4) z.2)) hsite
  have hrd := fkRectRefinedDartSite_reduce_four h4 pd
    (fkRectRefinedBoundaryCanonicalCenter R d.1) d.1.2 hnormald
  have hre := fkRectRefinedDartSite_reduce_four h4 pe
    (fkRectRefinedBoundaryCanonicalCenter R e.1) e.1.2 hnormale
  change fkRectBlackDartSite R d = fkRectBlackDartSite R e at hsite
  change (ZMod.castHom h4 (ZMod 4) (fkRectBlackDartSite R d).1,
      ZMod.castHom h4 (ZMod 4) (fkRectBlackDartSite R d).2) = _ at hreduce
  have hres : fkRectRefinedDartResidue pd d.1.2 =
      fkRectRefinedDartResidue pe e.1.2 := by
    rw [← hrd, ← hre]
    exact hreduce
  obtain ⟨hpair, hside⟩ :=
    fkRectRefinedDartResidue_injective_of_blackSide
      pd pe d.1.2 e.1.2
      (fkRectBlackDart_sideVertical R d)
      (fkRectBlackDart_sideVertical R e) hres
  have hcenter :
      let cd := fkRectRefinedBoundaryCanonicalCenter R d.1
      let ce := fkRectRefinedBoundaryCanonicalCenter R e.1
      (((cd.1 : Int) : ZMod L), ((cd.2 : Int) : ZMod L)) =
        (((ce.1 : Int) : ZMod L), ((ce.2 : Int) : ZMod L)) := by
    dsimp only
    apply Prod.ext
    · have hx := congrArg Prod.fst hsite
      unfold fkRectBlackDartSite fkRectIntegralSquarePointMod at hx
      dsimp only at hx
      have hx' := congrArg (fun z : ZMod L =>
        z - ((fkRectRefinedSideOffset d.1.2).1 : ZMod L)) hx
      rw [hside] at hx'
      push_cast at hx'
      simpa [fkRectRefinedDartPoint] using hx'
    · have hy := congrArg Prod.snd hsite
      unfold fkRectBlackDartSite fkRectIntegralSquarePointMod at hy
      dsimp only at hy
      have hy' := congrArg (fun z : ZMod L =>
        z - ((fkRectRefinedSideOffset d.1.2).2 : ZMod L)) hy
      rw [hside] at hy'
      push_cast at hy'
      simpa [fkRectRefinedDartPoint] using hy'
  have hedge : fkRectTorusMedialEdgeEquiv R d.1.1 =
      fkRectTorusMedialEdgeEquiv R e.1.1 := by
    apply fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq R _ _ (0, 0)
    dsimp only
    simpa [fkRectRefinedBoundaryCanonicalCenter,
      fkRectSquareDeckTranslation] using hcenter
  have hvertex : d.1.1 = e.1.1 :=
    (fkRectTorusMedialEdgeEquiv R).injective hedge
  apply Subtype.ext
  apply Prod.ext hvertex hside




theorem fkRectBlackDart_eq_of_shiftedSite_eq
    (R : FKRectTorus) (u : Int × Int)
    (d e : FKMedialBlackDart R.medialTorus)
    (hsite : fkRectBlackDartShiftedSite R u d =
      fkRectBlackDartSite R e) :
    d = e := by
  classical
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let A := fkRectSquareDeckTranslation R u
  let cd := fkRectRefinedBoundaryCanonicalCenter R d.1
  let ce := fkRectRefinedBoundaryCanonicalCenter R e.1
  let zd : Int × Int := (cd.1 + 4 * A.1, cd.2 + 4 * A.2)
  have h4 : 4 ∣ L := by
    refine ⟨fkRectSquareCoverSide R, ?_⟩
    simp [L]
  let pd := fkRectClosedPairingAtEdge
    (fkRectTorusMedialEdgeEquiv R d.1.1)
  let pe := fkRectClosedPairingAtEdge
    (fkRectTorusMedialEdgeEquiv R e.1.1)
  have hnormald : FKRectRefinedEdgeCenterNormal pd zd := by
    exact (fkRectRefinedBoundaryCanonicalCenter_normal R d.1).add_four
      A.1 A.2
  have hnormale : FKRectRefinedEdgeCenterNormal pe ce :=
    fkRectRefinedBoundaryCanonicalCenter_normal R e.1
  have hreduce := congrArg (fun z : ZMod L × ZMod L =>
    (ZMod.castHom h4 (ZMod 4) z.1,
      ZMod.castHom h4 (ZMod 4) z.2)) hsite
  have hrd := fkRectRefinedDartSite_reduce_four h4 pd zd d.1.2 hnormald
  have hre := fkRectRefinedDartSite_reduce_four h4 pe ce e.1.2 hnormale
  change fkRectIntegralSquarePointMod L
      (fkRectRefinedDartPoint zd d.1.2) =
    fkRectIntegralSquarePointMod L
      (fkRectRefinedDartPoint ce e.1.2) at hsite
  change
    (ZMod.castHom h4 (ZMod 4)
        (fkRectIntegralSquarePointMod L
          (fkRectRefinedDartPoint zd d.1.2)).1,
      ZMod.castHom h4 (ZMod 4)
        (fkRectIntegralSquarePointMod L
          (fkRectRefinedDartPoint zd d.1.2)).2) = _ at hreduce
  have hres : fkRectRefinedDartResidue pd d.1.2 =
      fkRectRefinedDartResidue pe e.1.2 := by
    rw [← hrd, ← hre]
    exact hreduce
  obtain ⟨-, hside⟩ :=
    fkRectRefinedDartResidue_injective_of_blackSide
      pd pe d.1.2 e.1.2
      (fkRectBlackDart_sideVertical R d)
      (fkRectBlackDart_sideVertical R e) hres
  have hcenter :
      (((zd.1 : Int) : ZMod L), ((zd.2 : Int) : ZMod L)) =
        (((ce.1 : Int) : ZMod L), ((ce.2 : Int) : ZMod L)) := by
    apply Prod.ext
    · have hx := congrArg Prod.fst hsite
      unfold fkRectIntegralSquarePointMod at hx
      dsimp only at hx
      have hx' := congrArg (fun z : ZMod L =>
        z - ((fkRectRefinedSideOffset d.1.2).1 : ZMod L)) hx
      rw [hside] at hx'
      push_cast at hx'
      simpa [fkRectRefinedDartPoint] using hx'
    · have hy := congrArg Prod.snd hsite
      unfold fkRectIntegralSquarePointMod at hy
      dsimp only at hy
      have hy' := congrArg (fun z : ZMod L =>
        z - ((fkRectRefinedSideOffset d.1.2).2 : ZMod L)) hy
      rw [hside] at hy'
      push_cast at hy'
      simpa [fkRectRefinedDartPoint] using hy'
  have hedge : fkRectTorusMedialEdgeEquiv R d.1.1 =
      fkRectTorusMedialEdgeEquiv R e.1.1 := by
    apply fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq R _ _ u
    dsimp [zd, cd, ce, A]
    dsimp [zd, cd, ce, A] at hcenter
    simpa [fkRectRefinedBoundaryCanonicalCenter] using hcenter
  have hvertex : d.1.1 = e.1.1 :=
    (fkRectTorusMedialEdgeEquiv R).injective hedge
  apply Subtype.ext
  apply Prod.ext hvertex hside



theorem fkRectBlackDart_eq_of_shiftedSite_eq_shiftedSite
    (R : FKRectTorus) (u v : Int × Int)
    (d e : FKMedialBlackDart R.medialTorus)
    (hsite : fkRectBlackDartShiftedSite R u d =
      fkRectBlackDartShiftedSite R v e) :
    d = e := by
  apply fkRectBlackDart_eq_of_shiftedSite_eq R (u - v) d e
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  apply Prod.ext
  · have hx := congrArg Prod.fst hsite
    change _ = _ at hx ⊢
    simp only [fkRectBlackDartShiftedSite, fkRectBlackDartShiftedPoint,
      fkRectBlackDartSite,
      fkRectIntegralSquarePointMod, fkRectRefinedDartPoint,
      fkRectSquareDeckTranslation, Prod.fst, Prod.snd,
      Prod.fst_sub, Prod.snd_sub] at hx ⊢
    push_cast at hx ⊢
    linear_combination hx
  · have hy := congrArg Prod.snd hsite
    change _ = _ at hy ⊢
    simp only [fkRectBlackDartShiftedSite, fkRectBlackDartShiftedPoint,
      fkRectBlackDartSite,
      fkRectIntegralSquarePointMod, fkRectRefinedDartPoint,
      fkRectSquareDeckTranslation, Prod.fst, Prod.snd,
      Prod.fst_sub, Prod.snd_sub] at hy ⊢
    push_cast at hy ⊢
    linear_combination hy



theorem fkRectBlackDartShiftedPoint_injective (R : FKRectTorus) :
    Function.Injective (fun z : (Int × Int) ×
      FKMedialBlackDart R.medialTorus =>
        fkRectBlackDartShiftedPoint R z.1 z.2) := by
  rintro ⟨u, d⟩ ⟨v, e⟩ hpoint
  have hsite : fkRectBlackDartShiftedSite R u d =
      fkRectBlackDartShiftedSite R v e := by
    unfold fkRectBlackDartShiftedSite
    change fkRectBlackDartShiftedPoint R u d =
      fkRectBlackDartShiftedPoint R v e at hpoint
    exact congrArg _ hpoint
  have hde := fkRectBlackDart_eq_of_shiftedSite_eq_shiftedSite
    R u v d e hsite
  subst e
  have hdeck : fkRectSquareDeckTranslation R u =
      fkRectSquareDeckTranslation R v := by
    have hx := congrArg Prod.fst hpoint
    have hy := congrArg Prod.snd hpoint
    simp only [fkRectBlackDartShiftedPoint, fkRectRefinedDartPoint,
      Prod.fst, Prod.snd] at hx hy
    apply Prod.ext
    · omega
    · omega
  have huv := fkRectSquareDeckHom_injective R hdeck
  subst v
  rfl



theorem fkRectRefinedDartPoint_localMate_eq_add_two_step
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) (c : Int × Int) :
    fkRectRefinedDartPoint c (fkMedialLocalMate pairing d).2 =
      ((fkRectRefinedDartPoint c d.2).1 +
          2 * StatMech.Onsager.ons_dirExponentX
            (fkMedialStrandDirection pairing d),
        (fkRectRefinedDartPoint c d.2).2 +
          2 * StatMech.Onsager.ons_dirExponentY
            (fkMedialStrandDirection pairing d)) := by
  rcases d with ⟨v, side⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkMedialLocalMate, fkMedialStrandDirection, hp,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring



theorem fkRectRefinedBoundaryStep_point
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) (c : Int × Int) :
    fkRectRefinedDartPoint
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2)
        (fkMedialBoundaryStep pairing d).2 =
      ((fkRectRefinedDartPoint c d.2).1 +
          2 * StatMech.Onsager.ons_dirExponentX
            (fkMedialStrandDirection pairing d),
        (fkRectRefinedDartPoint c d.2).2 +
          2 * StatMech.Onsager.ons_dirExponentY
            (fkMedialStrandDirection pairing d)) := by
  rw [show (fkMedialBoundaryStep pairing d).2 =
      (fkMedialBondMate T (fkMedialLocalMate pairing d)).2 by rfl]
  rw [fkRectRefinedDartPoint_bondMate T c
    (fkMedialLocalMate pairing d)]
  exact fkRectRefinedDartPoint_localMate_eq_add_two_step pairing d c

end
end StatMech.FrontierD
