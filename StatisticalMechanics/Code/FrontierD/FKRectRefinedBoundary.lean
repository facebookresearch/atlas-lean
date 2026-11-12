/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialBoundaryWalk











namespace StatMech.FrontierD

noncomputable section



def fkRectRefinedSideOffset : FKMedialSide → Int × Int
  | .west => (-1, -1)
  | .east => (1, 1)
  | .south => (-1, 1)
  | .north => (1, -1)



def fkRectRefinedDartPoint (c : Int × Int) (side : FKMedialSide) :
    Int × Int :=
  (c.1 + (fkRectRefinedSideOffset side).1,
    c.2 + (fkRectRefinedSideOffset side).2)



def fkRectRefinedBondCenter (c : Int × Int) (side : FKMedialSide) :
    Int × Int :=
  (c.1 + 2 * (fkRectRefinedSideOffset side).1,
    c.2 + 2 * (fkRectRefinedSideOffset side).2)


def fkRectMedialLocalMateSide (pairing : Bool) :
    FKMedialSide → FKMedialSide
  | .west => if pairing then .south else .north
  | .east => if pairing then .north else .south
  | .south => if pairing then .west else .east
  | .north => if pairing then .east else .west

@[simp] theorem fkMedialLocalMate_side
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLocalMate pairing d).2 =
      fkRectMedialLocalMateSide (pairing d.1) d.2 := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkRectMedialLocalMateSide, h]

theorem fkRectRefinedDartPoint_bondMate
    (T : EvenTorus) (c : Int × Int) (d : FKMedialDart T) :
    fkRectRefinedDartPoint
        (fkRectRefinedBondCenter c d.2)
        (fkMedialBondMate T d).2 =
      fkRectRefinedDartPoint c d.2 := by
  rcases d with ⟨v, side⟩
  cases side <;>
    simp [fkRectRefinedDartPoint, fkRectRefinedBondCenter,
      fkRectRefinedSideOffset, fkMedialBondMate] <;> ring_nf <;> simp


def fkRectRefinedLocalDarts (pairing : Bool) (c : Int × Int)
    (side : FKMedialSide) : List FKRectIntegralSquareDart :=
  let p := fkRectRefinedDartPoint c side
  match pairing, side with
  | false, .west | false, .south => [(p, 0), ((p.1 + 1, p.2), 0)]
  | false, .east | false, .north => [(p, 2), ((p.1 - 1, p.2), 2)]
  | true, .west | true, .north => [(p, 1), ((p.1, p.2 + 1), 1)]
  | true, .east | true, .south => [(p, 3), ((p.1, p.2 - 1), 3)]

private theorem fkRectRefinedTwoEast_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 + 2, p.2)
      [(p, 0), ((p.1 + 1, p.2), 0)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 0)
    (q := (p.1 + 1, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1 + 1, p.2), 0)
    (q := (p.1 + 2, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

private theorem fkRectRefinedTwoWest_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 2, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 2)
    (q := (p.1 - 1, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1 - 1, p.2), 2)
    (q := (p.1 - 2, p.2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

private theorem fkRectRefinedTwoNorth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 2)
      [(p, 1), ((p.1, p.2 + 1), 1)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 1)
    (q := (p.1, p.2 + 1)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1, p.2 + 1), 1)
    (q := (p.1, p.2 + 2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _

private theorem fkRectRefinedTwoSouth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 - 2)
      [(p, 3), ((p.1, p.2 - 1), 3)] := by
  refine FKRectIntegralSquareDartPath.cons (p, 3)
    (q := (p.1, p.2 - 1)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  refine FKRectIntegralSquareDartPath.cons ((p.1, p.2 - 1), 3)
    (q := (p.1, p.2 - 2)) ?_ ?_
  · simp [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring
  exact FKRectIntegralSquareDartPath.nil _



theorem fkRectRefinedLocalDarts_path
    (pairing : Bool) (c : Int × Int) (side : FKMedialSide) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c side)
      (fkRectRefinedDartPoint c
        (fkRectMedialLocalMateSide pairing side))
      (fkRectRefinedLocalDarts pairing c side) := by
  cases pairing <;> cases side
  · convert fkRectRefinedTwoEast_path
      (fkRectRefinedDartPoint c .west) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoWest_path
      (fkRectRefinedDartPoint c .east) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoEast_path
      (fkRectRefinedDartPoint c .south) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoWest_path
      (fkRectRefinedDartPoint c .north) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoNorth_path
      (fkRectRefinedDartPoint c .west) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoSouth_path
      (fkRectRefinedDartPoint c .east) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoSouth_path
      (fkRectRefinedDartPoint c .south) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring
  · convert fkRectRefinedTwoNorth_path
      (fkRectRefinedDartPoint c .north) using 1 <;>
      simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectMedialLocalMateSide] <;> ring


def fkRectRefinedBoundaryCenterAfter {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    FKMedialDart T → (Int × Int) → Nat → (Int × Int)
  | _, c, 0 => c
  | d, c, n + 1 =>
      fkRectRefinedBoundaryCenterAfter pairing
        (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c
          (fkMedialLocalMate pairing d).2) n


def fkRectRefinedBoundaryDarts {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    FKMedialDart T → (Int × Int) → Nat →
      List FKRectIntegralSquareDart
  | _, _, 0 => []
  | d, c, n + 1 =>
      fkRectRefinedLocalDarts (pairing d.1) c d.2 ++
        fkRectRefinedBoundaryDarts pairing
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c
            (fkMedialLocalMate pairing d).2) n


theorem fkRectRefinedBoundaryDarts_path {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) (n : Nat) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint
        (fkRectRefinedBoundaryCenterAfter pairing d c n)
        (((fkMedialBoundaryStep pairing)^[n] d).2))
      (fkRectRefinedBoundaryDarts pairing d c n) := by
  induction n generalizing d c with
  | zero =>
      exact FKRectIntegralSquareDartPath.nil _
  | succ n ih =>
      let localSide := (fkMedialLocalMate pairing d).2
      let next := fkMedialBoundaryStep pairing d
      let nextCenter := fkRectRefinedBondCenter c localSide
      have hlocal : FKRectIntegralSquareDartPath
          (fkRectRefinedDartPoint c d.2)
          (fkRectRefinedDartPoint c localSide)
          (fkRectRefinedLocalDarts (pairing d.1) c d.2) := by
        simpa [localSide, fkMedialLocalMate_side] using
          fkRectRefinedLocalDarts_path (pairing d.1) c d.2
      have htail := ih next nextCenter
      have hbond : fkRectRefinedDartPoint nextCenter next.2 =
          fkRectRefinedDartPoint c localSide := by
        simpa [next, nextCenter, localSide] using
          fkRectRefinedDartPoint_bondMate T c
            (fkMedialLocalMate pairing d)
      rw [hbond] at htail
      have happend := hlocal.append htail
      simpa [fkRectRefinedBoundaryDarts,
        fkRectRefinedBoundaryCenterAfter, next, nextCenter, localSide,
        Function.iterate_succ_apply] using happend



theorem fkRectRefinedBoundaryOrbitDarts_path {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint
        (fkRectRefinedBoundaryCenterAfter pairing d c
          (orderOf (fkMedialBoundaryStep pairing))) d.2)
      (fkRectRefinedBoundaryDarts pairing d c
        (orderOf (fkMedialBoundaryStep pairing))) := by
  have h := fkRectRefinedBoundaryDarts_path pairing d c
    (orderOf (fkMedialBoundaryStep pairing))
  have hpow : (fkMedialBoundaryStep pairing) ^
      orderOf (fkMedialBoundaryStep pairing) = 1 :=
    pow_orderOf_eq_one _
  have hreturn :
      (fkMedialBoundaryStep pairing)^[orderOf
          (fkMedialBoundaryStep pairing)] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa only [hpow, Equiv.Perm.one_apply]
  rwa [hreturn] at h





theorem fkRectCanonicalSquareEdgeStep_eq
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      if fkRectClosedPairingAtEdge e then (-1, 0) else (0, 1) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  all_goals
    simp [fkRectLiftedIndexedEdgeEnds, fkRectClosedPairingAtEdge,
      fkRectSquareDevelopPoint, hy]
  · obtain ⟨k, hk⟩ := hy
    omega
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
    omega
  · obtain ⟨k, hk⟩ := hy
    omega
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
    omega



theorem fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation
    (R : FKRectTorus) (e : R.EdgeIndex) :
    if fkRectClosedPairingAtEdge e then
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 =
          fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 =
          fkRectMedialWestPrimal R e
    else
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 =
          fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 =
          fkRectMedialEastPrimal R e := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectMedialEastPrimal, fkRectMedialWestPrimal,
      fkRectClosedPairingAtEdge, hy]


def fkRectRefinedPrimalEdgeStart (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  (4 * p.1, 4 * p.2)


def fkRectRefinedPrimalEdgeEnd (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  (4 * p.1, 4 * p.2)


def fkRectRefinedPrimalEdgeCenter (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  (2 * (p.1 + q.1), 2 * (p.2 + q.2))


def fkRectRefinedPrimalEdgeDarts (R : FKRectTorus) (e : R.EdgeIndex) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedPrimalEdgeStart R e
  if fkRectClosedPairingAtEdge e then
    [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  else
    [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]

private theorem fkRectRefinedFourWest_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 4, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
        ((p.1 - 3, p.2), 2)] := by
  have h1 := fkRectRefinedTwoWest_path p
  have h2 := fkRectRefinedTwoWest_path (p.1 - 2, p.2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring

private theorem fkRectRefinedFourNorth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 4)
      [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
        ((p.1, p.2 + 3), 1)] := by
  have h1 := fkRectRefinedTwoNorth_path p
  have h2 := fkRectRefinedTwoNorth_path (p.1, p.2 + 2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring



theorem fkRectRefinedFourEast_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 + 4, p.2)
      [(p, 0), ((p.1 + 1, p.2), 0), ((p.1 + 2, p.2), 0),
        ((p.1 + 3, p.2), 0)] := by
  have h1 := fkRectRefinedTwoEast_path p
  have h2 := fkRectRefinedTwoEast_path (p.1 + 2, p.2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring



theorem fkRectRefinedFourWest_path_public (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 4, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
        ((p.1 - 3, p.2), 2)] :=
  fkRectRefinedFourWest_path p



theorem fkRectRefinedFourNorth_path_public (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 4)
      [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
        ((p.1, p.2 + 3), 1)] :=
  fkRectRefinedFourNorth_path p



theorem fkRectRefinedFourSouth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 - 4)
      [(p, 3), ((p.1, p.2 - 1), 3), ((p.1, p.2 - 2), 3),
        ((p.1, p.2 - 3), 3)] := by
  have h1 := fkRectRefinedTwoSouth_path p
  have h2 := fkRectRefinedTwoSouth_path (p.1, p.2 - 2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring



theorem fkRectRefinedPrimalEdgeDarts_path
    (R : FKRectTorus) (e : R.EdgeIndex) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e)
      (fkRectRefinedPrimalEdgeDarts R e) := by
  have hend : fkRectRefinedPrimalEdgeEnd R e =
      if fkRectClosedPairingAtEdge e then
        ((fkRectRefinedPrimalEdgeStart R e).1 - 4,
          (fkRectRefinedPrimalEdgeStart R e).2)
      else
        ((fkRectRefinedPrimalEdgeStart R e).1,
          (fkRectRefinedPrimalEdgeStart R e).2 + 4) := by
    have h := fkRectCanonicalSquareEdgeStep_eq R e
    by_cases hp : fkRectClosedPairingAtEdge e = true
    · simp [hp] at h ⊢
      unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
    · have hp' : fkRectClosedPairingAtEdge e = false :=
        Bool.eq_false_of_not_eq_true hp
      simp [hp, hp'] at h ⊢
      unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  rw [hend]
  by_cases hp : fkRectClosedPairingAtEdge e
  · simpa [fkRectRefinedPrimalEdgeDarts, hp] using
      fkRectRefinedFourWest_path (fkRectRefinedPrimalEdgeStart R e)
  · simpa [fkRectRefinedPrimalEdgeDarts, hp] using
      fkRectRefinedFourNorth_path (fkRectRefinedPrimalEdgeStart R e)

end

end StatMech.FrontierD
