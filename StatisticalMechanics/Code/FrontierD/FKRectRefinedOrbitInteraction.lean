/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedInteractionCore
import Code.FrontierD.FKMedialBoundaryOrbitVisits








open scoped BigOperators
open Equiv Finset

namespace StatMech.FrontierD

noncomputable section


def permOrbitSignedVisitTrace {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (sigma : Perm alpha) (d a b : alpha) : Nat -> Int
  | 0 => 0
  | n + 1 =>
      (if d = a then 1 else 0) - (if d = b then 1 else 0) +
        permOrbitSignedVisitTrace sigma (sigma d) a b n

theorem permOrbitSignedVisitTrace_eq_sum_range
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (sigma : Perm alpha) (d a b : alpha) (n : Nat) :
    permOrbitSignedVisitTrace sigma d a b n =
      Finset.sum (range n) fun i =>
        ((if (sigma ^ i) d = a then 1 else 0) : Int) -
          (if (sigma ^ i) d = b then 1 else 0) := by
  induction n generalizing d with
  | zero => simp [permOrbitSignedVisitTrace]
  | succ n ih =>
      rw [permOrbitSignedVisitTrace, ih, sum_range_succ']
      have htail :
          (∑ i ∈ range n,
            (((if (sigma ^ i) (sigma d) = a then 1 else 0) : Int) -
              (if (sigma ^ i) (sigma d) = b then 1 else 0))) =
            ∑ i ∈ range n,
              (((if (sigma ^ (i + 1)) d = a then 1 else 0) : Int) -
                (if (sigma ^ (i + 1)) d = b then 1 else 0)) := by
        apply sum_congr rfl
        intro i hi
        simp only [pow_succ, Perm.mul_apply]
      rw [htail]
      simp only [Nat.one_add, pow_zero, Perm.one_apply]
      abel



theorem permOrbitSignedVisitTrace_orderOf
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (sigma : Perm alpha) (d a b : alpha) :
    permOrbitSignedVisitTrace sigma d a b (orderOf sigma) =
      (permOrbitVisitCount sigma d a : Int) -
        permOrbitVisitCount sigma d b := by
  rw [permOrbitSignedVisitTrace_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold permOrbitVisitCount
  push_cast
  rw [Finset.sum_sub_distrib]



def fkRectRefinedBoundaryLocalInteraction
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex) : Int :=
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  fkRectRefinedRawInteraction
    ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map
      (fkRectIntegralSquareDartMod L))
    ((fkRectRefinedPrimalEdgeDarts R e).map
      (fkRectIntegralSquareDartMod L))



def fkRectRefinedBoundaryInteractionTrace
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Int
  | _, _, 0 => 0
  | d, c, n + 1 =>
      fkRectRefinedBoundaryLocalInteraction R pairing d c e +
        fkRectRefinedBoundaryInteractionTrace R pairing e
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n



def FKRectRefinedBoundaryHasLocalVisitInteraction
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Prop
  | _, _, 0 => True
  | d, c, n + 1 =>
      fkRectRefinedBoundaryLocalInteraction R pairing d c e =
          (if d = a then 1 else 0) - (if d = b then 1 else 0) ∧
        FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n



theorem fkRectRefinedRawInteraction_boundaryDarts
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex) (n : Nat) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c n).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      fkRectRefinedBoundaryInteractionTrace R pairing e d c n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryDarts,
      fkRectRefinedBoundaryInteractionTrace,
      fkRectRefinedRawInteraction]
  | succ n ih =>
      simp only [fkRectRefinedBoundaryDarts,
        List.map_append, fkRectRefinedRawInteraction_append_left,
        fkRectRefinedBoundaryInteractionTrace]
      rw [ih]
      rfl




theorem fkRectRefinedBoundaryInteractionTrace_eq_signedVisits
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int),
      fkRectRefinedBoundaryLocalInteraction R pairing d' c' e =
        (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
      permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryInteractionTrace,
      permOrbitSignedVisitTrace]
  | succ n ih =>
      rw [fkRectRefinedBoundaryInteractionTrace,
        permOrbitSignedVisitTrace, hlocal, ih]



theorem fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction
      R pairing e a b d c n) :
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
      permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryInteractionTrace,
      permOrbitSignedVisitTrace]
  | succ n ih =>
      rcases hlocal with ⟨hone, htail⟩
      rw [fkRectRefinedBoundaryInteractionTrace,
        permOrbitSignedVisitTrace, hone, ih _ _ htail]


theorem fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int)
    (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int),
      fkRectRefinedBoundaryLocalInteraction R pairing d' c' e =
        (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c
            (orderOf (fkMedialBoundaryStep pairing))).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      (fkMedialBoundaryOrbitVisitCount pairing d a : Int) -
        fkMedialBoundaryOrbitVisitCount pairing d b := by
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  rw [fkRectRefinedBoundaryInteractionTrace_eq_signedVisits
    R pairing e a b d c _ hlocal]
  exact permOrbitSignedVisitTrace_orderOf _ _ _ _



theorem fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_of_hasLocal
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int)
    (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b
      d c (orderOf (fkMedialBoundaryStep pairing))) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c
            (orderOf (fkMedialBoundaryStep pairing))).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      (fkMedialBoundaryOrbitVisitCount pairing d a : Int) -
        fkMedialBoundaryOrbitVisitCount pairing d b := by
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  rw [fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal
    R pairing e a b d c _ hlocal]
  exact permOrbitSignedVisitTrace_orderOf _ _ _ _

end

end StatMech.FrontierD
