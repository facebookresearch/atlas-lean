/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKLoopSixVertexLocalCorrespondence

open SimpleGraph

namespace StatMech.FrontierD


inductive FKMedialSide
  | west | east | south | north
deriving DecidableEq, Fintype

abbrev FKMedialDart (T : EvenTorus) := T.Vertex × FKMedialSide


def fkMedialLocalMate (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) : FKMedialDart T :=
  match pairing d.1, d.2 with
  | false, .west => (d.1, .north)
  | false, .north => (d.1, .west)
  | false, .east => (d.1, .south)
  | false, .south => (d.1, .east)
  | true, .west => (d.1, .south)
  | true, .south => (d.1, .west)
  | true, .east => (d.1, .north)
  | true, .north => (d.1, .east)


def fkMedialBondMate (T : EvenTorus)
    (d : FKMedialDart T) : FKMedialDart T :=
  match d.2 with
  | .west =>
      ((SixVertexArrows.cyclicPred T.width_pos d.1.1, d.1.2), .east)
  | .east =>
      ((finitePeriodicSucc T.width_pos d.1.1, d.1.2), .west)
  | .south =>
      ((d.1.1, SixVertexArrows.cyclicPred T.height_pos d.1.2), .north)
  | .north =>
      ((d.1.1, finitePeriodicSucc T.height_pos d.1.2), .south)

theorem finitePeriodicSucc_cyclicPred {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    finitePeriodicSucc hN (SixVertexArrows.cyclicPred hN i) = i := by
  obtain ⟨j, hj⟩ := (svFinitePeriodicSuccEquiv hN).surjective i
  change finitePeriodicSucc hN j = i at hj
  rw [<- hj, svCyclicPred_finitePeriodicSucc]

theorem fkMedialLocalMate_involutive
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialLocalMate pairing (fkMedialLocalMate pairing d) = d := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, h]

theorem fkMedialBondMate_involutive
    (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialBondMate T (fkMedialBondMate T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp [fkMedialBondMate, finitePeriodicSucc_cyclicPred]
  · simp [fkMedialBondMate, svCyclicPred_finitePeriodicSucc]
  · simp [fkMedialBondMate, finitePeriodicSucc_cyclicPred]
  · simp [fkMedialBondMate, svCyclicPred_finitePeriodicSucc]

theorem fkMedialLocalMate_ne
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialLocalMate pairing d ≠ d := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, h]

theorem fkMedialBondMate_ne (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialBondMate T d ≠ d := by
  rcases d with ⟨v, side⟩
  cases side <;> simp [fkMedialBondMate]



def fkMedialLoopGraph (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) : SimpleGraph (FKMedialDart T) where
  Adj d e :=
    (e = fkMedialLocalMate pairing d ∨ d = fkMedialLocalMate pairing e) ∨
      (e = fkMedialBondMate T d ∨ d = fkMedialBondMate T e)
  symm := by
    intro d e h
    rcases h with (h | h) | (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨by
    intro d h
    rcases h with (h | h) | (h | h)
    · exact fkMedialLocalMate_ne pairing d h.symm
    · exact fkMedialLocalMate_ne pairing d h.symm
    · exact fkMedialBondMate_ne T d h.symm
    · exact fkMedialBondMate_ne T d h.symm⟩

noncomputable instance fkMedialLoopGraphDecidableRel
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) :
    DecidableRel (fkMedialLoopGraph T pairing).Adj := Classical.decRel _

theorem fkMedialLoopGraph_adj_iff
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d e : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Adj d e ↔
      e = fkMedialLocalMate pairing d ∨ e = fkMedialBondMate T d := by
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · left
      rw [h, fkMedialLocalMate_involutive]
    · exact Or.inr h
    · right
      rw [h, fkMedialBondMate_involutive]
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

theorem fkMedialLocalMate_ne_bondMate
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialLocalMate pairing d ≠ fkMedialBondMate T d := by
  rcases d with ⟨v, side⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialBondMate, hp]

theorem fkMedialLoopGraph_neighborFinset
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).neighborFinset d =
      {fkMedialLocalMate pairing d, fkMedialBondMate T d} := by
  ext e
  rw [SimpleGraph.mem_neighborFinset, fkMedialLoopGraph_adj_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]



theorem fkMedialLoopGraph_degree_eq_two
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).degree d = 2 := by
  rw [<- SimpleGraph.card_neighborFinset_eq_degree,
    fkMedialLoopGraph_neighborFinset]
  simp [fkMedialLocalMate_ne_bondMate T pairing d]



abbrev FKMedialLoop (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) :=
  (fkMedialLoopGraph T pairing).ConnectedComponent

noncomputable def fkMedialLoopCount (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) : Nat :=
  Nat.card (FKMedialLoop T pairing)


def fkMedialDartIncoming (omega : SixVertexArrows T)
    (d : FKMedialDart T) : Bool :=
  match d.2 with
  | .west => fkLoopWestIncoming omega d.1
  | .east => fkLoopEastIncoming omega d.1
  | .south => fkLoopSouthIncoming omega d.1
  | .north => fkLoopNorthIncoming omega d.1



theorem fkMedialDartIncoming_localMate_ne
    (pairing : FKMedialLoopPairing T) (omega : SixVertexArrows T)
    (hcompat : forall v,
      fkLoopPairingCompatible (pairing v) omega v)
    (d : FKMedialDart T) :
    fkMedialDartIncoming omega (fkMedialLocalMate pairing d) ≠
      fkMedialDartIncoming omega d := by
  rcases d with ⟨v, side⟩
  have h := hcompat v
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialDartIncoming,
      fkLoopPairingCompatible, hp] at h ⊢ <;> tauto


theorem fkMedialDartIncoming_bondMate_ne
    (T : EvenTorus) (omega : SixVertexArrows T)
    (d : FKMedialDart T) :
    fkMedialDartIncoming omega (fkMedialBondMate T d) ≠
      fkMedialDartIncoming omega d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming,
      svCyclicPred_finitePeriodicSucc]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming,
      svCyclicPred_finitePeriodicSucc]



theorem fkMedialLoopGraph_adj_incoming_ne
    (pairing : FKMedialLoopPairing T) (omega : SixVertexArrows T)
    (hcompat : forall v,
      fkLoopPairingCompatible (pairing v) omega v)
    {d e : FKMedialDart T} (hde : (fkMedialLoopGraph T pairing).Adj d e) :
    fkMedialDartIncoming omega d ≠ fkMedialDartIncoming omega e := by
  rcases hde with (rfl | h) | (rfl | h)
  · exact (fkMedialDartIncoming_localMate_ne
      pairing omega hcompat d).symm
  · subst d
    exact fkMedialDartIncoming_localMate_ne pairing omega hcompat e
  · exact (fkMedialDartIncoming_bondMate_ne T omega d).symm
  · subst d
    exact fkMedialDartIncoming_bondMate_ne T omega e



def fkOrientedLoopVerticalFlux (T : EvenTorus)
    (omega : SixVertexArrows T) : Int :=
  ∑ i : Fin T.width,
    if omega.vertical (i, svFinLast T.height_pos) then (1 : Int) else -1

theorem sum_bool_toNat_eq_sixVertexUpCount
    {N : Nat} (x : SixVertexRow N) :
    (∑ i, (x i).toNat) = sixVertexUpCount x := by
  classical
  unfold sixVertexUpCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x i <;> simp [h]


theorem fkOrientedLoopVerticalFlux_eq_charge
    (T : EvenTorus) (omega : SixVertexArrows T) :
    fkOrientedLoopVerticalFlux T omega =
      2 * (sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) -
        (T.width : Int) := by
  classical
  let x := svTorusVerticalRows T omega (svFinLast T.height_pos)
  have hc : (∑ i, (x i).toNat) = sixVertexUpCount x :=
    sum_bool_toNat_eq_sixVertexUpCount x
  have hcInt : (∑ i, ((x i).toNat : Int)) =
      (sixVertexUpCount x : Int) := by
    exact_mod_cast hc
  unfold fkOrientedLoopVerticalFlux
  change (∑ i, if x i then (1 : Int) else -1) = _
  calc
    (∑ i, if x i then (1 : Int) else -1) =
        ∑ i, (2 * ((x i).toNat : Int) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases x i <;> simp
    _ = 2 * (∑ i, ((x i).toNat : Int)) - (T.width : Int) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    _ = 2 * (sixVertexUpCount x : Int) - (T.width : Int) := by
      rw [hcInt]



theorem fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge
    (T : EvenTorus) (omega : SixVertexArrows T)
    (r : Nat) (hr : r <= T.width / 2)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) =
        T.width / 2 - r) :
    fkOrientedLoopVerticalFlux T omega = -(2 * (r : Int)) := by
  rw [fkOrientedLoopVerticalFlux_eq_charge, hsector]
  obtain ⟨k, hk⟩ := T.width_even
  have hw : T.width / 2 = k := by omega
  have hrk : r <= k := by rwa [<- hw]
  rw [hw, hk]
  push_cast [Nat.cast_sub hrk]
  ring

end StatMech.FrontierD
