/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.FKMedialCheckerboard

open Equiv Finset SimpleGraph
namespace StatMech.FrontierD
noncomputable section
variable {T : EvenTorus}

namespace FKMedialTurningFiber

local instance medialLoopDecidableEq
    (pairing : FKMedialLoopPairing T) :
    DecidableEq (FKMedialLoop T pairing) := Classical.decEq _


def turnSign (pairing incoming : Bool) : Int :=
  if pairing = incoming then 1 else -1

def vertexTurn (pairing : Bool) (a : SixVertexArrows T) (v : T.Vertex) : Int :=
  turnSign pairing (fkLoopWestIncoming a v) +
    turnSign pairing (fkLoopEastIncoming a v)

theorem local_eq (lam : Real) (pairing : Bool) (a : SixVertexArrows T)
    (v : T.Vertex) (h : fkLoopPairingCompatible pairing a v) :
    fkOrientedLoopLocalWeight lam pairing a v =
      Real.exp ((lam / 4) * vertexTurn pairing a v) := by
  generalize hw : a.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at h ⊢
  generalize he : a.horizontal v = e at h ⊢
  generalize hs : a.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at h ⊢
  generalize hn : a.vertical v = n at h ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkOrientedLoopLocalWeight, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.IsCType, turnSign, vertexTurn,
      hw, he, hs, hn] at h ⊢ <;> ring_nf at *

def modeIncoming (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) : Bool :=
  if mode ((fkMedialLoopGraph T pairing).connectedComponentMk d) then
    !fkMedialCheckerColor d
  else fkMedialCheckerColor d

def arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) : SixVertexArrows T where
  horizontal v := !modeIncoming pairing mode (v, .east)
  vertical v := !modeIncoming pairing mode (v, .north)

theorem modeIncoming_bondMate (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) :
    (!modeIncoming pairing mode (fkMedialBondMate T d)) =
      modeIncoming pairing mode d := by
  have hcomp : (fkMedialLoopGraph T pairing).connectedComponentMk
      (fkMedialBondMate T d) =
      (fkMedialLoopGraph T pairing).connectedComponentMk d := by
    apply SimpleGraph.ConnectedComponent.sound
    exact (show (fkMedialLoopGraph T pairing).Adj
      (fkMedialBondMate T d) d by
        rw [fkMedialLoopGraph_adj_iff]
        right
        rw [fkMedialBondMate_involutive]).reachable
  have hcolor := fkMedialCheckerColor_bondMate_ne T d
  unfold modeIncoming
  rw [hcomp]
  generalize hm : mode ((fkMedialLoopGraph T pairing).connectedComponentMk d) = m
  generalize hc : fkMedialCheckerColor d = c
  generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hcolor
  cases m <;> cases c <;> cases b <;> simp_all

theorem incoming_arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) :
    fkMedialDartIncoming (arrowsOfMode pairing mode) d =
      modeIncoming pairing mode d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp only [fkMedialDartIncoming, fkLoopWestIncoming, arrowsOfMode]
    exact modeIncoming_bondMate pairing mode ((i, j), .west)
  · simp [fkMedialDartIncoming, fkLoopEastIncoming, arrowsOfMode]
  · simp only [fkMedialDartIncoming, fkLoopSouthIncoming, arrowsOfMode]
    exact modeIncoming_bondMate pairing mode ((i, j), .south)
  · simp [fkMedialDartIncoming, fkLoopNorthIncoming, arrowsOfMode]

theorem compatible_arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    ∀ v, fkLoopPairingCompatible (pairing v)
      (arrowsOfMode pairing mode) v := by
  intro v
  cases hp : pairing v <;>
    simp only [fkLoopPairingCompatible, Bool.false_eq_true,
      ite_false, ite_true]
  · constructor
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .north)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .west) (v, .north) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .west)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .west) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .north) = b at hc ⊢
        cases a <;> cases b <;> simp_all

    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .south)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .east) (v, .south) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .east)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .east) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .south) = b at hc ⊢
        cases a <;> cases b <;> simp_all
  · constructor
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .south)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .west) (v, .south) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .west)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .west) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .south) = b at hc ⊢
        cases a <;> cases b <;> simp_all
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .north)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .east) (v, .north) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .east)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .east) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .north) = b at hc ⊢
        cases a <;> cases b <;> simp_all

private theorem eq_iff_eq_of_ne_ne {a b c d : Bool}
    (hab : a ≠ b) (hcd : c ≠ d) : (a = c ↔ b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem incoming_eq_color_iff_reachable
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialDartIncoming a d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming a e = fkMedialCheckerColor e) := by
  obtain ⟨w⟩ := hde
  induction w with
  | nil => exact Iff.rfl
  | @cons d e f hde w ih =>
      exact (eq_iff_eq_of_ne_ne
        (fkMedialLoopGraph_adj_incoming_ne pairing a hcompat hde)
        (fkMedialLoopGraph_adj_checkerColor_ne T pairing hde)).trans ih

def modeOfArrows (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T) (C : FKMedialLoop T pairing) : Bool :=
  fkMedialDartIncoming a C.out ^^ fkMedialCheckerColor C.out

theorem modeIncoming_modeOfArrows
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v)
    (d : FKMedialDart T) :
    modeIncoming pairing (modeOfArrows pairing a) d =
      fkMedialDartIncoming a d := by
  let C := (fkMedialLoopGraph T pairing).connectedComponentMk d
  have hreach : (fkMedialLoopGraph T pairing).Reachable C.out d :=
    SimpleGraph.ConnectedComponent.exact C.out_eq
  have hiff := incoming_eq_color_iff_reachable pairing a hcompat hreach
  unfold modeIncoming modeOfArrows
  change (if fkMedialDartIncoming a C.out ^^ fkMedialCheckerColor C.out
      then !fkMedialCheckerColor d else fkMedialCheckerColor d) = _
  generalize ho : fkMedialDartIncoming a C.out = o at hiff ⊢
  generalize hco : fkMedialCheckerColor C.out = co at hiff ⊢
  generalize hd : fkMedialDartIncoming a d = x at hiff ⊢
  generalize hcd : fkMedialCheckerColor d = cd at hiff ⊢
  cases o <;> cases co <;> cases x <;> cases cd <;> simp_all

theorem arrowsOfMode_modeOfArrows
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
    arrowsOfMode pairing (modeOfArrows pairing a) = a := by
  ext v
  · have h := modeIncoming_modeOfArrows pairing a hcompat (v, .east)
    change (!modeIncoming pairing (modeOfArrows pairing a) (v, .east)) =
      a.horizontal v
    rw [h]
    simp [fkMedialDartIncoming, fkLoopEastIncoming]
  · have h := modeIncoming_modeOfArrows pairing a hcompat (v, .north)
    change (!modeIncoming pairing (modeOfArrows pairing a) (v, .north)) =
      a.vertical v
    rw [h]
    simp [fkMedialDartIncoming, fkLoopNorthIncoming]

theorem modeOfArrows_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    modeOfArrows pairing (arrowsOfMode pairing mode) = mode := by
  funext C
  unfold modeOfArrows
  rw [incoming_arrowsOfMode]
  unfold modeIncoming
  have hm : mode ((fkMedialLoopGraph T pairing).connectedComponentMk C.out) =
      mode C := congrArg mode C.out_eq
  rw [hm]
  change ((if mode C then !fkMedialCheckerColor C.out
    else fkMedialCheckerColor C.out) ^^ fkMedialCheckerColor C.out) = mode C
  cases mode C <;> cases fkMedialCheckerColor C.out <;> rfl

def modeEquivCompatibleArrows (pairing : FKMedialLoopPairing T) :
    (FKMedialLoop T pairing → Bool) ≃
      {a : SixVertexArrows T //
        ∀ v, fkLoopPairingCompatible (pairing v) a v} where
  toFun mode := ⟨arrowsOfMode pairing mode,
    compatible_arrowsOfMode pairing mode⟩
  invFun a := modeOfArrows pairing a.1
  left_inv := modeOfArrows_arrowsOfMode pairing
  right_inv := by
    intro a
    apply Subtype.ext
    exact arrowsOfMode_modeOfArrows pairing a.1 a.2

noncomputable def componentTurn (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ v : T.Vertex, (
    (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
      then turnSign (pairing v) (fkMedialDartIncoming a (v, .west)) else 0) +
    (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
      then turnSign (pairing v) (fkMedialDartIncoming a (v, .east)) else 0))

def canonicalComponentTurn (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing) : Int :=
  componentTurn pairing (arrowsOfMode pairing fun _ => false) C

private theorem turnSign_not (p b : Bool) :
    turnSign p (!b) = -turnSign p b := by
  cases p <;> cases b <;> rfl

theorem componentTurn_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (C : FKMedialLoop T pairing) :
    componentTurn pairing (arrowsOfMode pairing mode) C =
      if mode C then -canonicalComponentTurn pairing C
      else canonicalComponentTurn pairing C := by
  classical
  have hpoint (v : T.Vertex) :
      ((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
          then turnSign (pairing v)
            (fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west))
          else 0) +
        (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
          then turnSign (pairing v)
            (fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east))
          else 0)) =
      if mode C then
        -((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .west))
            else 0) +
          (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .east))
            else 0))
      else
        ((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .west))
            else 0) +
          (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .east))
            else 0)) := by
    by_cases hw : (fkMedialLoopGraph T pairing).connectedComponentMk
        (v, .west) = C <;>
      by_cases he : (fkMedialLoopGraph T pairing).connectedComponentMk
        (v, .east) = C
    all_goals rw [incoming_arrowsOfMode, incoming_arrowsOfMode,
      incoming_arrowsOfMode, incoming_arrowsOfMode]
    all_goals unfold modeIncoming
    all_goals simp only [hw, he, if_true, if_false]
    all_goals cases hm : mode C <;>
      cases hp : pairing v <;>
      cases hwc : fkMedialCheckerColor (v, .west) <;>
      cases hec : fkMedialCheckerColor (v, .east) <;>
      simp [turnSign]
  by_cases hm : mode C
  · rw [if_pos hm]
    unfold canonicalComponentTurn componentTurn
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simpa [hm] using hpoint v
  · rw [if_neg hm]
    unfold canonicalComponentTurn componentTurn
    apply Finset.sum_congr rfl
    intro v hv
    simpa [hm] using hpoint v

theorem sum_componentTurn_eq_vertexTurn
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T) :
    (∑ C : FKMedialLoop T pairing, componentTurn pairing a C) =
      ∑ v : T.Vertex, vertexTurn (pairing v) a v := by
  classical
  unfold componentTurn vertexTurn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_add_distrib, fkMedialDartIncoming]

theorem orientedLoopWeight_eq_exp_sum_componentTurn
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
    fkOrientedLoopPairingWeight lam pairing a =
      Real.exp ((lam / 4) *
        ∑ C : FKMedialLoop T pairing, componentTurn pairing a C) := by
  unfold fkOrientedLoopPairingWeight
  simp_rw [local_eq lam _ a _ (hcompat _)]
  rw [← Real.exp_sum]
  rw [sum_componentTurn_eq_vertexTurn]
  congr 1
  push_cast
  simpa using (Finset.mul_sum (s := Finset.univ)
    (f := fun v : T.Vertex => (vertexTurn (pairing v) a v : Real))
    (lam / 4)).symm

theorem orientedLoopWeight_arrowsOfMode
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    fkOrientedLoopPairingWeight lam pairing (arrowsOfMode pairing mode) =
      ∏ C : FKMedialLoop T pairing,
        if mode C then Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)
        else Real.exp ((lam / 4) * canonicalComponentTurn pairing C) := by
  rw [orientedLoopWeight_eq_exp_sum_componentTurn lam pairing _
    (compatible_arrowsOfMode pairing mode)]
  rw [show Real.exp ((lam / 4) *
        ∑ C : FKMedialLoop T pairing,
          componentTurn pairing (arrowsOfMode pairing mode) C) =
      ∏ C : FKMedialLoop T pairing,
        Real.exp ((lam / 4) *
          componentTurn pairing (arrowsOfMode pairing mode) C) by
    rw [← Real.exp_sum]
    congr 1
    push_cast
    simpa using (Finset.mul_sum (s := Finset.univ)
      (f := fun C : FKMedialLoop T pairing =>
        (componentTurn pairing (arrowsOfMode pairing mode) C : Real))
      (lam / 4))]
  apply Finset.prod_congr rfl
  intro C hC
  rw [componentTurn_arrowsOfMode]
  split <;> congr 1 <;> push_cast <;> ring

theorem sum_orientedLoopWeight_eq_sum_modes
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    (∑ a : SixVertexArrows T,
        fkOrientedLoopPairingWeight lam pairing a) =
      ∑ mode : (FKMedialLoop T pairing → Bool),
        fkOrientedLoopPairingWeight lam pairing
          (arrowsOfMode pairing mode) := by
  classical
  let p : SixVertexArrows T → Prop := fun a =>
    ∀ v, fkLoopPairingCompatible (pairing v) a v
  let f : SixVertexArrows T → Real := fun a =>
    fkOrientedLoopPairingWeight lam pairing a
  have hzero (a : SixVertexArrows T) (ha : ¬p a) : f a = 0 := by
    change ¬∀ v, fkLoopPairingCompatible (pairing v) a v at ha
    push Not at ha
    obtain ⟨v, hv⟩ := ha
    unfold f fkOrientedLoopPairingWeight
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [fkOrientedLoopLocalWeight, hv]
  calc
    (∑ a : SixVertexArrows T, f a) =
        ∑ a : SixVertexArrows T, if p a then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hpa : p a
      · rw [if_pos hpa]
      · rw [if_neg hpa, hzero a hpa]
    _ = (∑ a ∈ (Finset.univ.filter p), f a) := by
      symm
      simpa using Finset.sum_filter p f
    _ = ∑ a : {a : SixVertexArrows T // p a}, f a.1 := by
      symm
      simpa using Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (SixVertexArrows T))) (p := p) f
    _ = ∑ mode : (FKMedialLoop T pairing → Bool),
          f (arrowsOfMode pairing mode) := by
      symm
      apply Fintype.sum_equiv (modeEquivCompatibleArrows pairing)
      intro mode
      rfl

theorem sum_orientedLoopWeight_eq_turningProduct
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    (∑ a : SixVertexArrows T,
        fkOrientedLoopPairingWeight lam pairing a) =
      ∏ C : FKMedialLoop T pairing,
        (Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
          Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)) := by
  rw [sum_orientedLoopWeight_eq_sum_modes]
  simp_rw [orientedLoopWeight_arrowsOfMode]
  let g : FKMedialLoop T pairing → Bool → Real := fun C b =>
    if b then Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)
    else Real.exp ((lam / 4) * canonicalComponentTurn pairing C)
  change (∑ x : (FKMedialLoop T pairing → Bool), ∏ C, g C (x C)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro C hC
  simp [g, add_comm]



theorem orientationFactor_eq_two_of_turn_eq_zero
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing)
    (hC : canonicalComponentTurn pairing C = 0) :
    Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
        Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) = 2 := by
  rw [hC]
  norm_num



theorem orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing)
    (hC : canonicalComponentTurn pairing C = 4 ∨
      canonicalComponentTurn pairing C = -4) :
      Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
        Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) =
      Real.exp lam + Real.exp (-lam) := by
  rcases hC with hC | hC
  · rw [hC]
    congr 1 <;> ring
  · rw [hC, add_comm]
    congr 1 <;> ring

end FKMedialTurningFiber

end
end StatMech.FrontierD
