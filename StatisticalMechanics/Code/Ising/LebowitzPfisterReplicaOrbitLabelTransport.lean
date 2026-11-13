/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms










open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaOrbitLabelTransportDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



structure LPReplicaProfileOrbitSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  allocation : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedRep : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedReflect : forall e :
    ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))
  selectedRep_subset : forall e, selectedRep e ⊆ allocation e
  selectedReflect_subset : forall e,
    selectedReflect e ⊆ Finset.univ \ allocation e

@[ext]
theorem LPReplicaProfileOrbitSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {s t : LPReplicaProfileOrbitSlotState G sites q}
    (ha : s.allocation = t.allocation)
    (hr : s.selectedRep = t.selectedRep)
    (ht : s.selectedReflect = t.selectedReflect) : s = t := by
  cases s
  cases t
  cases ha
  cases hr
  cases ht
  rfl


def lpReplicaProfileOrbitSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q) :
    LPReplicaProfileOrbitSlotState G sites q where
  allocation := fun e =>
    (s.allocation e \ s.selectedRep e) ∪ s.selectedReflect e
  selectedRep := s.selectedReflect
  selectedReflect := s.selectedRep
  selectedRep_subset := by
    intro e x hx
    exact Finset.mem_union_right _ hx
  selectedReflect_subset := by
    intro e x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmove
    rw [Finset.mem_union] at hmove
    rcases hmove with hremain | hreflect
    · exact (Finset.mem_sdiff.mp hremain).2 hx
    · have hxalloc := s.selectedRep_subset e hx
      have hreflect' := s.selectedReflect_subset e hreflect
      exact (Finset.mem_sdiff.mp hreflect').2 hxalloc



theorem lpReplicaProfileOrbitSlotMove_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive (lpReplicaProfileOrbitSlotMove G sites q) := by
  intro s
  cases s with
  | mk allocation selectedRep selectedReflect hrep hreflect =>
      apply LPReplicaProfileOrbitSlotState.ext
      · funext e
        ext x
        have hR := hrep e
        have hT := hreflect e
        simp only [lpReplicaProfileOrbitSlotMove, Finset.mem_union,
          Finset.mem_sdiff]
        constructor
        · rintro ((⟨(hx | hx), hnT⟩) | hxR)
          · exact hx.1
          · exact False.elim (hnT hx)
          · exact hR hxR
        · intro hx
          by_cases hxR : x ∈ selectedRep e
          · exact Or.inr hxR
          · left
            refine ⟨Or.inl ⟨hx, hxR⟩, ?_⟩
            intro hxT
            exact (Finset.mem_sdiff.mp (hT hxT)).2 hx
      · rfl
      · rfl



def lpReplicaProfileOrbitSlotMoveEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaProfileOrbitSlotState G sites q ≃
      LPReplicaProfileOrbitSlotState G sites q where
  toFun := lpReplicaProfileOrbitSlotMove G sites q
  invFun := lpReplicaProfileOrbitSlotMove G sites q
  left_inv := lpReplicaProfileOrbitSlotMove_involutive G sites q
  right_inv := lpReplicaProfileOrbitSlotMove_involutive G sites q



def LPReplicaProfileOrbitSlotRealizes
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q) : Prop :=
  forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    (s.allocation e).card = m e.1 ∧
      (s.selectedRep e).card = p e.1 ∧
      (s.selectedReflect e).card =
        p (lpReplicaCurrentEdgeReflect G sites e.1)



theorem lpReplicaProfileOrbitSlotMove_allocation_card
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaProfileOrbitSlotState G sites q)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    ((lpReplicaProfileOrbitSlotMove G sites q s).allocation e).card =
      (s.allocation e).card - (s.selectedRep e).card +
        (s.selectedReflect e).card := by
  have hdisj : Disjoint
      (s.allocation e \ s.selectedRep e) (s.selectedReflect e) := by
    rw [Finset.disjoint_left]
    intro x hx hT
    have hxalloc := (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp (s.selectedReflect_subset e hT)).2 hxalloc
  change ((s.allocation e \ s.selectedRep e) ∪
    s.selectedReflect e).card = _
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff_of_subset (s.selectedRep_subset e)]



theorem lpReplicaProfileOrbitSlotRealizes_move_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m)
    (s : LPReplicaProfileOrbitSlotState G sites q) :
    LPReplicaProfileOrbitSlotRealizes G sites q m p s ↔
      LPReplicaProfileOrbitSlotRealizes G sites q
        (lpReplicaPartialReflectProfile G sites m p)
        (fun e => p (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaProfileOrbitSlotMove G sites q s) := by
  constructor
  · intro h e
    have he := h e
    rw [lpReplicaProfileOrbitSlotMove_allocation_card]
    unfold lpReplicaPartialReflectProfile
    simp only [lpReplicaProfileOrbitSlotMove]
    refine ⟨by omega, he.2.2, ?_⟩
    rw [lpReplicaCurrentEdgeReflect_involutive]
    exact he.2.1
  · intro h e
    have he := h e
    rw [lpReplicaProfileOrbitSlotMove_allocation_card] at he
    unfold lpReplicaPartialReflectProfile at he
    simp only [lpReplicaProfileOrbitSlotMove] at he
    have hRle : (s.selectedRep e).card ≤ (s.allocation e).card :=
      Finset.card_le_card (s.selectedRep_subset e)
    have hR := he.2.2
    rw [lpReplicaCurrentEdgeReflect_involutive] at hR
    refine ⟨?_, hR, he.2.1⟩
    have hpe := hp e.1
    change p e.1 ≤ m e.1 at hpe
    omega



def LPReplicaProfileOrbitSelectedLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ L : LPReplicaProfileOrbitLabel G sites q m,
    forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      {R : Finset (Fin (q e.1)) //
        R ⊆ L e ∧ R.card = p e.1} ×
      {T : Finset (Fin (q e.1)) //
        T ⊆ Finset.univ \ L e ∧
          T.card = p (lpReplicaCurrentEdgeReflect G sites e.1)}


def lpReplicaProfileOrbitLabelRepEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    Fin (m e.1) ↪ Fin (q e.1) :=
  ((L e).1.orderIsoOfFin
      (Finset.mem_powersetCard.mp (L e).2).2).toEmbedding.trans
    (Function.Embedding.subtype _)



def lpReplicaProfileOrbitLabelReflectEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    Fin (m (lpReplicaCurrentEdgeReflect G sites e.1)) ↪ Fin (q e.1) := by
  have hcard : (Finset.univ \ (L e).1).card =
      m (lpReplicaCurrentEdgeReflect G sites e.1) := by
    have hq := congrFun hm e.1
    unfold lpReplicaSymmetrizedProfile at hq
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin,
      (Finset.mem_powersetCard.mp (L e).2).2]
    omega
  exact ((Finset.univ \ (L e).1).orderIsoOfFin hcard).toEmbedding.trans
    (Function.Embedding.subtype _)



def lpReplicaProfileOrbitSelectedLabelOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaProfileOrbitSelectedLabel G sites q m
      (StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P) := by
  refine ⟨L, fun e => ?_⟩
  let R := (lpReplicaCopyIndicesAtEdge G sites m P e.1).map
    (lpReplicaProfileOrbitLabelRepEmbedding G sites q m L e)
  let T := (lpReplicaCopyIndicesAtEdge G sites m P
      (lpReplicaCurrentEdgeReflect G sites e.1)).map
    (lpReplicaProfileOrbitLabelReflectEmbedding G sites q m hm L e)
  refine (⟨R, ?_, ?_⟩, ⟨T, ?_, ?_⟩)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact ((L e).1.orderIsoOfFin
      (Finset.mem_powersetCard.mp (L e).2).2 i).2
  · rw [Finset.card_map, card_lpReplicaCopyIndicesAtEdge]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact ((Finset.univ \ (L e).1).orderIsoOfFin (by
      have hq := congrFun hm e.1
      unfold lpReplicaSymmetrizedProfile at hq
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin,
        (Finset.mem_powersetCard.mp (L e).2).2]
      omega) i).2
  · rw [Finset.card_map, card_lpReplicaCopyIndicesAtEdge]



def lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaProfileOrbitSelectedLabel G sites q m p ≃
      {s : LPReplicaProfileOrbitSlotState G sites q //
        LPReplicaProfileOrbitSlotRealizes G sites q m p s} where
  toFun x := ⟨{
    allocation := fun e => x.1 e
    selectedRep := fun e => (x.2 e).1.1
    selectedReflect := fun e => (x.2 e).2.1
    selectedRep_subset := fun e => (x.2 e).1.2.1
    selectedReflect_subset := fun e => (x.2 e).2.2.1
  }, fun e => ⟨(Finset.mem_powersetCard.mp (x.1 e).2).2,
    (x.2 e).1.2.2, (x.2 e).2.2.2⟩⟩
  invFun x := ⟨fun e => ⟨x.1.allocation e,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (x.2 e).1⟩⟩,
    fun e =>
      (⟨x.1.selectedRep e, x.1.selectedRep_subset e, (x.2 e).2.1⟩,
       ⟨x.1.selectedReflect e, x.1.selectedReflect_subset e,
        (x.2 e).2.2⟩)⟩
  left_inv x := by
    apply Sigma.ext
    · funext e
      rfl
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply LPReplicaProfileOrbitSlotState.ext <;> rfl




def lpReplicaProfileOrbitSelectedLabelPartialReflectEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    p <= m ->
    LPReplicaProfileOrbitSelectedLabel G sites q m p ≃
      LPReplicaProfileOrbitSelectedLabel G sites q
        (lpReplicaPartialReflectProfile G sites m p)
        (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) := by
  intro hp
  let source := lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
    G sites q m p
  let target := lpReplicaProfileOrbitSelectedLabelEquivSlotFiber G sites q
    (lpReplicaPartialReflectProfile G sites m p)
    (fun e => p (lpReplicaCurrentEdgeReflect G sites e))
  let move : {s : LPReplicaProfileOrbitSlotState G sites q //
      LPReplicaProfileOrbitSlotRealizes G sites q m p s} ≃
      {s : LPReplicaProfileOrbitSlotState G sites q //
        LPReplicaProfileOrbitSlotRealizes G sites q
          (lpReplicaPartialReflectProfile G sites m p)
          (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) s} := {
    toFun := fun s => ⟨lpReplicaProfileOrbitSlotMove G sites q s.1,
      (lpReplicaProfileOrbitSlotRealizes_move_iff
        G sites q m p hp s.1).mp s.2⟩
    invFun := fun s => ⟨lpReplicaProfileOrbitSlotMove G sites q s.1, by
      apply (lpReplicaProfileOrbitSlotRealizes_move_iff
        G sites q m p hp
          (lpReplicaProfileOrbitSlotMove G sites q s.1)).mpr
      rw [lpReplicaProfileOrbitSlotMove_involutive G sites q s.1]
      exact s.2⟩
    left_inv := fun s => by
      apply Subtype.ext
      exact lpReplicaProfileOrbitSlotMove_involutive G sites q s.1
    right_inv := fun s => by
      apply Subtype.ext
      exact lpReplicaProfileOrbitSlotMove_involutive G sites q s.1
  }
  exact source.trans (move.trans target.symm)



noncomputable def lpReplicaProfileOrbitLabelPartialReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaProfileOrbitLabel G sites q
      (lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)) :=
  ((lpReplicaProfileOrbitSelectedLabelPartialReflectEquiv G sites q m
      (StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P)
      (StatMech.Sharpness.FluxEdgeCopy.profileFlux_le
        (lpReplicaCurrentGraph G sites) m P))
    (lpReplicaProfileOrbitSelectedLabelOfCopies G sites q m hm P L)).1

end

end StatMech.Ising
