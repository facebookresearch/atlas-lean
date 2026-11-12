/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian
import Code.Universality.IsingFermionicSquareBoundaryGeometry











namespace StatMech.Universality

open Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquarePerimeterDirection :
    FKIsingSquareBoundarySide → FKIsingSquareDirection
  | .bottom => .east
  | .right => .north
  | .top => .west
  | .left => .south

private theorem fkIsingSquarePerimeterDirection_available
    (n : Nat) (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareBoundaryVertex n (side, k))
      (fkIsingSquarePerimeterDirection side) := by
  have hk := k.isLt
  cases side <;>
    simp [fkIsingSquarePerimeterDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] <;> omega


def fkIsingSquarePerimeterEdge (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionEdge n (fkIsingSquareBoundaryVertex n (side, k))
    (fkIsingSquarePerimeterDirection side)
    (fkIsingSquarePerimeterDirection_available n side k)



def fkIsingSquarePerimeterRetainedSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .west
  | .right => .east
  | .top => .east
  | .left => .west


def fkIsingSquarePerimeterCancelledSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .east
  | .right => .west
  | .top => .west
  | .left => .east




def fkIsingSquarePerimeterInteriorSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .west
  | .right => .west
  | .top => .east
  | .left => .east



def fkIsingSquarePerimeterInteriorRadialDart
    (n : Nat) (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterInteriorSide side), by
    have hk := k.isLt
    cases side <;>
      simp [fkIsingSquarePerimeterInteriorSide,
        fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega⟩


def fkIsingSquarePerimeterInteriorRadialIncidence
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : FKIsingSquareInteriorRadialIncidence n hn :=
  Quot.mk _ (fkIsingSquarePerimeterInteriorRadialDart n side k)

theorem fkIsingSquarePerimeterInteriorRadialEndpoint
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) =
      fkIsingSquareBoundaryVertex n (side, k) := by
  change fkIsingSquareDartEndpoint n
    (fkIsingSquarePerimeterInteriorRadialDart n side k).1 = _
  cases side <;>
    simp [fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]



theorem fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) (hfree : side ≠ .left) :
    fkIsingSquareFullFaceFixedBoundary n
      (fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  have hkey := fkIsingSquareFullFaceOfRadialIncidence_key n hn
    (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)
  change fkIsingSquareInteriorCellKey n _ =
    fkIsingSquareWedgeFaceKey n
      (fkIsingSquarePerimeterInteriorRadialDart n side k).1 at hkey
  unfold fkIsingSquareFullFaceFixedBoundary
  cases side with
  | bottom =>
      left
      have h := congrArg Prod.snd hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | right =>
      right; left
      have h := congrArg Prod.fst hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | top =>
      right; right
      have h := congrArg Prod.snd hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | left => exact False.elim (hfree rfl)


def fkIsingSquarePerimeterMarkedCut (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Prop :=
  (side = .bottom ∧ k.1 = 0) ∨
    (side = .top ∧ k.1 + 1 = 2 * n)


def FKIsingSquarePerimeterCancellationAt (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Prop :=
  ¬ fkIsingSquarePerimeterMarkedCut n side k ∧
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)) = 0


def FKIsingSquarePerimeterCancellation (n : Nat) (hn : 0 < n) : Prop :=
  ∀ side k, ¬ fkIsingSquarePerimeterMarkedCut n side k →
    FKIsingSquarePerimeterCancellationAt n hn side k


structure FKIsingSquarePerimeterCancellationSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  paired_summand : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (pairing omega)
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side))




structure FKIsingSquarePerimeterGlobalPathSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  visited : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration (pairing omega) ↔
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side) :
          FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration omega
  mass : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (pairing omega) =
      (fkIsingSquareWiredDobrushinDomain n hn).criticalMass omega
  phase : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration omega →
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (pairing omega)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side))




structure FKIsingSquarePerimeterOppositeCarrierSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  mate : FKIsingSquareWiredCarrier n
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  visited : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration (pairing omega) ↔
      mate ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega
  mass : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (pairing omega) =
      (fkIsingSquareWiredDobrushinDomain n hn).criticalMass omega
  phase : ∀ omega,
    mate ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega →
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (pairing omega)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega mate



theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.paired_summand
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (S.pairing omega)
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        S.mate := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  change D.fermionicSummand (S.pairing omega) z =
    -D.fermionicSummand omega S.mate
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases hm : S.mate ∈ D.exploration omega
  · have hz : z ∈ D.exploration (S.pairing omega) :=
      (S.visited omega).2 hm
    rw [if_pos hz, if_pos hm, S.mass omega, S.phase omega hm]
    ring
  · have hz : z ∉ D.exploration (S.pairing omega) :=
      fun h ↦ hm ((S.visited omega).1 h)
    rw [if_neg hz, if_neg hm, neg_zero]



theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.observable_eq_neg_mate
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  unfold FKIsingDobrushinDomain.fermionicObservable
  calc
    ∑ omega, D.fermionicSummand omega z =
        ∑ omega, D.fermionicSummand (S.pairing omega) z := by
      exact (S.pairing.sum_comp (fun omega ↦ D.fermionicSummand omega z)).symm
    _ = ∑ omega, -D.fermionicSummand omega S.mate := by
      apply Finset.sum_congr rfl
      intro omega _
      exact S.paired_summand omega
    _ = -∑ omega, D.fermionicSummand omega S.mate := by simp



theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.cancellationAt_of_transport
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k)
    (htransport :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side))) :
    FKIsingSquarePerimeterCancellationAt n hn side k := by
  refine ⟨S.uncut, ?_⟩
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  have hneg : D.fermionicObservable z = -D.fermionicObservable z := by
    calc
      D.fermionicObservable z = -D.fermionicObservable S.mate := by
        simpa only [D, z] using S.observable_eq_neg_mate
      _ = -D.fermionicObservable z := by
        exact congrArg Neg.neg (by simpa only [D, z] using htransport)
  have htwo : (2 : Complex) * D.fermionicObservable z = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

def FKIsingSquarePerimeterGlobalPathSwitchingAt.toCancellationSwitching
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterGlobalPathSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationSwitchingAt n hn side k where
  uncut := S.uncut
  pairing := S.pairing
  paired_summand := by
    intro omega
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let z : FKIsingSquareWiredCarrier n :=
      .dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)
    change D.fermionicSummand (S.pairing omega) z =
      -D.fermionicSummand omega z
    unfold FKIsingDobrushinDomain.fermionicSummand
    by_cases hz : z ∈ D.exploration omega
    · have hz' : z ∈ D.exploration (S.pairing omega) :=
        (S.visited omega).2 hz
      rw [if_pos hz', if_pos hz, S.mass omega, S.phase omega hz]
      ring
    · have hz' : z ∉ D.exploration (S.pairing omega) := by
        exact fun h ↦ hz ((S.visited omega).1 h)
      rw [if_neg hz', if_neg hz, neg_zero]

theorem FKIsingSquarePerimeterCancellationSwitchingAt.cancellationAt
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterCancellationSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationAt n hn side k := by
  refine ⟨S.uncut, ?_⟩
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  let total := ∑ omega, D.fermionicSummand omega z
  have hreindex : (∑ omega, D.fermionicSummand omega z) =
      ∑ omega, D.fermionicSummand (S.pairing omega) z := by
    exact (S.pairing.sum_comp (fun omega ↦ D.fermionicSummand omega z)).symm
  have hneg : total = -total := by
    calc
      total = ∑ omega, D.fermionicSummand (S.pairing omega) z := hreindex
      _ = ∑ omega, -D.fermionicSummand omega z := by
        apply Finset.sum_congr rfl
        intro omega _
        exact S.paired_summand omega
      _ = -total := by simp [total]
  have htwo : (2 : Complex) * total = 0 := by
    linear_combination hneg
  have htotal : total = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [D, z, total, FKIsingDobrushinDomain.fermionicObservable] using htotal

theorem FKIsingSquarePerimeterGlobalPathSwitchingAt.cancellationAt
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterGlobalPathSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationAt n hn side k :=
  S.toCancellationSwitching.cancellationAt




theorem isingF_west_ne_zero_of_ne_zero (X : Complex) (hX : X ≠ 0) :
    isingF 0 X ≠ 0 := by
  intro h
  simp only [isingF] at h
  have hs : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)))
  field_simp [hs] at h
  have hzero : (Real.sqrt 2 : Complex) * 0 = 0 := by ring
  rw [hzero] at h
  have hcoef : (Real.sqrt 2 : Complex) + 1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp at hr
    have hp := Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)
    linarith
  exact hX ((mul_eq_zero.mp h).resolve_right hcoef)



theorem isingF_east_ne_zero_of_ne_zero (X : Complex) (hX : X ≠ 0) :
    isingF 1 X ≠ 0 := by
  intro h
  simp only [isingF] at h
  have hs : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)))
  field_simp [hs] at h
  rw [isingLambda_sq] at h
  have hzero : X = 0 := by simpa using h
  exact hX hzero




theorem fkIsingSquarePerimeter_configIdentity_not_signReversing
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (hne : (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)) ≠ 0) :
    ¬ ∀ rho,
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
          ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) := by
  intro h
  have hself := h omega
  simp only [Equiv.refl_apply] at hself
  apply hne
  have htwo : (2 : Complex) *
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)



theorem fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc
    (n : Nat) (k : Fin (2 * n)) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquarePerimeterEdge n .left k,
          fkIsingSquarePerimeterCancelledSide .left)) := by
  have hm := fkIsingSquareDartEndpoint_mem n
    (fkIsingSquarePerimeterEdge n .left k,
      fkIsingSquarePerimeterCancelledSide .left)
  simp only [fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDirectionEdge] at hm ⊢
  rw [Sym2.mem_iff] at hm
  rcases hm with hm | hm
  · rw [hm]
    rfl
  · rw [hm]
    simp [fkIsingSquareWiredArc, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]



theorem fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n .left k,
        fkIsingSquarePerimeterCancelledSide .left) :
      FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (FK.edgeSetConfig ∅) := by
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  rw [← fkIsingSquareWiredCompletedLoopGraph_reachable_iff]
  apply fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels
  · simp [fkIsingSquareWiredCarrierPrimalLabel,
      fkIsingSquareWiredArc, fkIsingSquareMarkedA]
  · exact fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc n k




theorem fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (FK.edgeSetConfig ∅)
        (.dart (fkIsingSquarePerimeterEdge n .left k,
          fkIsingSquarePerimeterCancelledSide .left)) ≠ 0 := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n .left k,
      fkIsingSquarePerimeterCancelledSide .left)
  have hzOrder : z ∈
      fkIsingSquareWiredExplorationOrder n hn (FK.edgeSetConfig ∅) := by
    simpa only [z] using
      fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration
        n hn k
  have hz : z ∈ D.exploration (FK.edgeSetConfig ∅) := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hzOrder
  have hmassR : 0 < D.criticalMass (FK.edgeSetConfig ∅) := by
    unfold FKIsingDobrushinDomain.criticalMass bcProb
    exact div_pos
      (bcWeight_pos (fkSquareBoxPlanar n).G D.wiring
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.1
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.2
        (by norm_num) _)
      (bcZ_pos (fkSquareBoxPlanar n).G D.wiring
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.1
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.2
        (by norm_num))
  have hmass : (D.criticalMass (FK.edgeSetConfig ∅) : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt hmassR
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hz]
  exact mul_ne_zero hmass (Complex.exp_ne_zero _)



theorem fkIsingSquarePerimeter_configIdentity_not_signReversing_empty_left
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    ¬ ∀ rho,
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
          ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho)
          (.dart (fkIsingSquarePerimeterEdge n .left k,
            fkIsingSquarePerimeterCancelledSide .left)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho
          (.dart (fkIsingSquarePerimeterEdge n .left k,
            fkIsingSquarePerimeterCancelledSide .left)) := by
  exact fkIsingSquarePerimeter_configIdentity_not_signReversing
    n hn .left k (FK.edgeSetConfig ∅)
      (fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero
        n hn k)

theorem fkIsingSquarePerimeterEdge_axis (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareOrientedEdge n
      (fkIsingSquarePerimeterEdge n side k)).axis =
      match side with
      | .bottom | .top => .horizontal
      | .right | .left => .vertical := by
  cases side <;>
    simp only [fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection] <;>
    rw [fkIsingSquareOrientedEdge_directionEdge] <;> rfl

theorem fkIsingSquarePerimeterRetained_tangent (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) =
      fkIsingSquareBoundaryTangent side := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨h, -, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, h, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, h, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨h, -, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h



def fkIsingSquareWiredBoundaryMedialObservable
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : Complex :=
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterRetainedSide side))



noncomputable def isingFermionicBoundaryVertexNormSqFactor : Real :=
  2 * Real.sqrt 2 / (1 + Real.sqrt 2)

theorem isingFermionicBoundaryVertexNormSqFactor_pos :
    0 < isingFermionicBoundaryVertexNormSqFactor := by
  unfold isingFermionicBoundaryVertexNormSqFactor
  positivity



theorem isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor :
    Real.sqrt 2 / 2 * isingFermionicBoundaryVertexNormSqFactor =
      isingFermionicGhostCoefficient := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
  unfold isingFermionicBoundaryVertexNormSqFactor
  unfold isingFermionicGhostCoefficient
  field_simp
  nlinarith




noncomputable def fkIsingSquareWiredBoundaryVertexSquareRepresentative
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : Complex :=
  (Real.sqrt isingFermionicBoundaryVertexNormSqFactor : Complex) *
    fkIsingSquareWiredBoundaryMedialObservable n hn side k

theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        Complex.normSq
          (fkIsingSquareWiredBoundaryMedialObservable n hn side k) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative,
    Complex.normSq_mul]
  have hfactor : 0 <= isingFermionicBoundaryVertexNormSqFactor :=
    isingFermionicBoundaryVertexNormSqFactor_pos.le
  simp [Complex.normSq_ofReal, Real.mul_self_sqrt hfactor]



theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterRetainedSide side)) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq]
  rw [← mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]
  rfl



theorem fkIsingSquareWiredBoundaryMedialObservable_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 =
      (fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
  unfold fkIsingSquareWiredBoundaryMedialObservable
  rw [← fkIsingSquarePerimeterRetained_tangent n hn side k]
  exact fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn _



theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k ^ 2 =
      (isingFermionicBoundaryVertexNormSqFactor *
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterRetainedSide side)) : Real) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative]
  have hfactor : 0 <= isingFermionicBoundaryVertexNormSqFactor :=
    isingFermionicBoundaryVertexNormSqFactor_pos.le
  have hsqrt := Real.sq_sqrt hfactor
  calc
    _ = (isingFermionicBoundaryVertexNormSqFactor : Complex) *
          (fkIsingSquareBoundaryTangent side *
            fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2) := by
      rw [mul_pow]
      rw [show (Real.sqrt isingFermionicBoundaryVertexNormSqFactor :
          Complex) ^ 2 = isingFermionicBoundaryVertexNormSqFactor by
        exact_mod_cast hsqrt]
      ring
    _ = _ := by
      rw [fkIsingSquareWiredBoundaryMedialObservable_square]
      norm_cast



theorem fkIsingSquareWiredBoundaryMedialObservable_exists_nonnegative_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareBoundaryTangent side *
          fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 =
        (t : Complex) := by
  refine ⟨fkIsingSquareWiredPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterRetainedSide side)),
    fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _, ?_⟩
  exact fkIsingSquareWiredBoundaryMedialObservable_square n hn side k



theorem fkIsingSquareWiredPerimeterInterior_face_sub_vertex
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterInteriorSide side)) := by
  let e := fkIsingSquarePerimeterInteriorRadialIncidence n hn side k
  have h := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e
  rw [fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k] at h
  simpa only [e, fkIsingSquarePerimeterInteriorRadialIncidence,
    fkIsingSquareInteriorRadialIncrement_mk,
    fkIsingSquarePerimeterInteriorRadialDart] using h


theorem fkIsingSquareWiredPerimeterInterior_vertex_le_face
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareBoundaryVertex n (side, k)) ≤
      FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn
          (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  let e := fkIsingSquarePerimeterInteriorRadialIncidence n hn side k
  have h := FKIsingSquareFullIntegratedPrimitive.vertex_le_face n hn e
  rw [fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k] at h
  exact h


theorem fkIsingSquareWiredPerimeterInterior_face_sub_vertex_nonneg
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    0 ≤ FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) := by
  rw [fkIsingSquareWiredPerimeterInterior_face_sub_vertex n hn side k]
  exact fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _

namespace FKIsingSquareFullIntegratedPrimitive




theorem vertex_modifiedLaplacian_nonpos_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (vertexPrimitive n hn) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - vertexPrimitive n hn x) <= 0 := by
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
    split_ifs <;> omega
  rw [show fkIsingSquareFullVertexGraph n = (fkSquareBoxPlanar n).G from rfl]
  simp [isingFermionicGhostRate, hmult]
  exact vertex_laplacian_nonpos_of_interior n hn x
    heast hnorth hwest hsouth




theorem face_modifiedLaplacian_nonneg_of_interior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (facePrimitive n hn) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - facePrimitive n hn c) := by
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 0 := by
    unfold fkIsingSquareFullFaceGhostMultiplicity
    split_ifs <;> omega
  simp [isingFermionicGhostRate, hmult]
  exact face_laplacian_nonneg_of_interior n hn c
    heast hnorth hwest hsouth

end FKIsingSquareFullIntegratedPrimitive

theorem fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareWiredFullMedialObservable n hn
        (fkIsingSquarePerimeterEdge n side k) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) := by
  rcases h with ⟨-, hzero⟩
  cases side <;>
    simp only [fkIsingSquarePerimeterCancelledSide] at hzero <;>
    simp [fkIsingSquareWiredFullMedialObservable,
      fkIsingSquarePerimeterRetainedSide, hzero]

theorem fkIsingSquareWiredFullMedialObservable_boundary_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredFullMedialObservable n hn
          (fkIsingSquarePerimeterEdge n side k) ^ 2 =
      (fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
  rw [fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation
    n hn side k h]
  rw [← fkIsingSquarePerimeterRetained_tangent n hn side k]
  exact fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn _

theorem fkIsingSquareWiredFullMedialObservable_exists_nonnegative_boundary_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareBoundaryTangent side *
          fkIsingSquareWiredFullMedialObservable n hn
            (fkIsingSquarePerimeterEdge n side k) ^ 2 = (t : Complex) := by
  refine ⟨fkIsingSquareWiredPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterRetainedSide side)),
    fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _, ?_⟩
  exact fkIsingSquareWiredFullMedialObservable_boundary_square n hn side k h

private theorem normSq_proj_I_eq_negI_of_proj_neg_one_eq_zero
    (F : Complex) (h : isingProj (-1) F = 0) :
    Complex.normSq (isingProj Complex.I F) =
      Complex.normSq (isingProj (-Complex.I) F) := by
  have hi := congrArg Complex.im h
  simp [isingProj] at hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hi ⊢
  rw [hi]
  ring

private theorem normSq_proj_I_eq_negI_of_proj_one_eq_zero
    (F : Complex) (h : isingProj 1 F = 0) :
    Complex.normSq (isingProj Complex.I F) =
      Complex.normSq (isingProj (-Complex.I) F) := by
  have hr := congrArg Complex.re h
  simp [isingProj] at hr
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr ⊢
  rw [hr]
  ring

private theorem normSq_proj_one_eq_neg_one_of_proj_negI_eq_zero
    (F : Complex) (h : isingProj (-Complex.I) F = 0) :
    Complex.normSq (isingProj 1 F) =
      Complex.normSq (isingProj (-1) F) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [isingProj] at hr hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr hi ⊢
  rw [show F.re = -F.im by linarith]
  ring

private theorem normSq_proj_one_eq_neg_one_of_proj_I_eq_zero
    (F : Complex) (h : isingProj Complex.I F = 0) :
    Complex.normSq (isingProj 1 F) =
      Complex.normSq (isingProj (-1) F) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [isingProj] at hr hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr hi ⊢
  rw [show F.re = F.im by linarith]


theorem fkIsingSquareWiredPerimeter_south_increment_eq_north_of_cancellation
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k, .south)) =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k, .north)) := by
  let e := fkIsingSquarePerimeterEdge n side k
  let F := fkIsingSquareWiredFullMedialObservable n hn e
  have hzero := h.2
  have hproj : isingProj
      (fkIsingSquareWiredDirectedTangent n hn
        (.dart (e, fkIsingSquarePerimeterCancelledSide side))) F = 0 := by
    rw [fkIsingSquareWiredFullMedialObservable_projection]
    exact hzero
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, hE, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_I_eq_negI_of_proj_neg_one_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hE] using hproj
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, -, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_one_eq_neg_one_of_proj_negI_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hW] using hproj
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, -, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_I_eq_negI_of_proj_one_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hW] using hproj
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, hE, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_one_eq_neg_one_of_proj_I_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hE] using hproj

def fkIsingSquarePerimeterFirstIndex (n : Nat) (hn : 0 < n) : Fin (2 * n) :=
  ⟨0, by omega⟩

def fkIsingSquarePerimeterLastIndex (n : Nat) (hn : 0 < n) : Fin (2 * n) :=
  ⟨2 * n - 1, by omega⟩

@[simp] theorem fkIsingSquarePerimeterMarkedCut_bottom_first
    (n : Nat) (hn : 0 < n) :
    fkIsingSquarePerimeterMarkedCut n .bottom
      (fkIsingSquarePerimeterFirstIndex n hn) := by
  exact Or.inl ⟨rfl, rfl⟩

@[simp] theorem fkIsingSquarePerimeterMarkedCut_top_last
    (n : Nat) (hn : 0 < n) :
    fkIsingSquarePerimeterMarkedCut n .top
      (fkIsingSquarePerimeterLastIndex n hn) := by
  right
  constructor
  · rfl
  · simp [fkIsingSquarePerimeterLastIndex]
    omega

theorem fkIsingSquareWiredSourceDart_eq_perimeter_bottom_first
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredSourceDart n hn =
      (fkIsingSquarePerimeterEdge n .bottom
        (fkIsingSquarePerimeterFirstIndex n hn), .south) := by
  apply Prod.ext
  · apply Subtype.ext
    change s(fkIsingSquareMarkedA n,
        fkIsingSquareNeighbor n (fkIsingSquareMarkedA n) .east
          (fkIsingSquareMarkedA_east_available n hn)) =
      s(fkIsingSquareBoundaryVertex n
          (.bottom, fkIsingSquarePerimeterFirstIndex n hn),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n
            (.bottom, fkIsingSquarePerimeterFirstIndex n hn)) .east
          (fkIsingSquarePerimeterDirection_available n .bottom
            (fkIsingSquarePerimeterFirstIndex n hn)))
    simp [fkIsingSquarePerimeterFirstIndex, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedA]
  · rfl

theorem fkIsingSquareWiredTerminalDart_eq_perimeter_top_last
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredTerminalDart n hn =
      (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn), .west) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDirectionEdge]
    change s(fkIsingSquareMarkedB n,
        fkIsingSquareNeighbor n (fkIsingSquareMarkedB n) .east
          (fkIsingSquareMarkedB_east_available n hn)) =
      s(fkIsingSquareBoundaryVertex n
          (.top, fkIsingSquarePerimeterLastIndex n hn),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n
            (.top, fkIsingSquarePerimeterLastIndex n hn)) .west
          (fkIsingSquarePerimeterDirection_available n .top
            (fkIsingSquarePerimeterLastIndex n hn)))
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [fkIsingSquarePerimeterLastIndex,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareMarkedB] <;> omega
  · rfl

theorem fkIsingSquareWired_top_marked_cancelled_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn),
        fkIsingSquarePerimeterCancelledSide .top)) = 1 := by
  simp only [fkIsingSquarePerimeterCancelledSide]
  rw [← fkIsingSquareWiredTerminalDart_eq_perimeter_top_last]
  exact fkIsingSquareWired_terminalDart_observable n hn

end

end StatMech.Universality
