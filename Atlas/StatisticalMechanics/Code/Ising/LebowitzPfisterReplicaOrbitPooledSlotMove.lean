/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor
import Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport













open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPooledSlotMoveDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



structure LPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  profile : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  orbit : lpReplicaSymmetrizedProfile G sites profile = q
  selected : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  selected_le : selected <= profile
  slots : LPReplicaProfileOrbitSlotState G sites q
  realizes : LPReplicaProfileOrbitSlotRealizes G sites q
    profile selected slots

@[ext]
theorem LPReplicaPooledSelectedSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {x y : LPReplicaPooledSelectedSlotState G sites q}
    (hprofile : x.profile = y.profile)
    (hselected : x.selected = y.selected)
    (hslots : x.slots = y.slots) : x = y := by
  cases x
  cases y
  cases hprofile
  cases hselected
  cases hslots
  rfl

local instance instDecidableEqLPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    DecidableEq (LPReplicaPooledSelectedSlotState G sites q) :=
  Classical.decEq _




noncomputable instance instFintypeLPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaPooledSelectedSlotState G sites q) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Profile := {m : H.edgeFinset -> Nat //
    lpReplicaSymmetrizedProfile G sites m = q}
  let Selected := {p : H.edgeFinset -> Nat // p <= q}
  let SlotCoord := (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) ->
    Finset (Fin (q e.1))
  let Target := Profile × Selected ×
    (SlotCoord × SlotCoord × SlotCoord)
  letI : Fintype Profile := lpReplicaProfileOrbitFintype G sites q
  letI : Fintype Selected :=
    StatMech.Sharpness.instFintypeLe H q
  letI : Fintype SlotCoord := by
    dsimp only [SlotCoord]
    infer_instance
  let encode : LPReplicaPooledSelectedSlotState G sites q -> Target := fun z =>
    (⟨z.profile, z.orbit⟩,
      ⟨z.selected, fun e => z.selected_le e |>.trans
        (lpReplicaProfile_le_of_symmetrizedProfile_eq G sites z.orbit e)⟩,
      (z.slots.allocation, z.slots.selectedRep, z.slots.selectedReflect))
  exact Fintype.ofInjective encode (by
    intro x y hxy
    apply LPReplicaPooledSelectedSlotState.ext
    · exact congrArg (fun z => z.1.1) hxy
    · exact congrArg (fun z => z.2.1.1) hxy
    · apply LPReplicaProfileOrbitSlotState.ext
      · exact congrArg (fun z => z.2.2.1) hxy
      · exact congrArg (fun z => z.2.2.2.1) hxy
      · exact congrArg (fun z => z.2.2.2.2) hxy)



def LPReplicaPooledSelectedOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q} =>
    Sigma fun a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      p <= m.1} =>
      LPReplicaProfileOrbitSelectedLabel G sites q m.1 a.1



def lpReplicaPooledSelectedOrbitLabelEquivSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaPooledSelectedOrbitLabel G sites q ≃
      LPReplicaPooledSelectedSlotState G sites q where
  toFun z := {
    profile := z.1.1
    orbit := z.1.2
    selected := z.2.1.1
    selected_le := z.2.1.2
    slots := (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.1.1 z.2.1.1 z.2.2).1
    realizes := (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.1.1 z.2.1.1 z.2.2).2
  }
  invFun z := ⟨⟨z.profile, z.orbit⟩, ⟨⟨z.selected, z.selected_le⟩,
    (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q z.profile z.selected).symm ⟨z.slots, z.realizes⟩⟩⟩
  left_inv z := by
    rcases z with ⟨m, a, L⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    exact (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber
      G sites q m.1 a.1).left_inv L
  right_inv z := by
    apply LPReplicaPooledSelectedSlotState.ext <;> try rfl

noncomputable instance instFintypeLPReplicaPooledSelectedOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaPooledSelectedOrbitLabel G sites q) :=
  Fintype.ofEquiv (LPReplicaPooledSelectedSlotState G sites q)
    (lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm




def lpReplicaPooledSelectedSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaPooledSelectedSlotState G sites q) :
    LPReplicaPooledSelectedSlotState G sites q where
  profile := lpReplicaPartialReflectProfile G sites z.profile z.selected
  orbit := (lpReplicaSymmetrizedProfile_partialReflect G sites
    z.profile z.selected z.selected_le).trans z.orbit
  selected := fun e =>
    z.selected (lpReplicaCurrentEdgeReflect G sites e)
  selected_le := lpReplicaReflectSubprofile_le_partialReflectProfile
    G sites z.profile z.selected
  slots := lpReplicaProfileOrbitSlotMove G sites q z.slots
  realizes := (lpReplicaProfileOrbitSlotRealizes_move_iff
    G sites q z.profile z.selected z.selected_le z.slots).mp z.realizes


theorem lpReplicaPooledSelectedSlotMove_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive (lpReplicaPooledSelectedSlotMove G sites q) := by
  intro z
  apply LPReplicaPooledSelectedSlotState.ext
  · exact lpReplicaPartialReflectProfile_involutive
      G sites z.profile z.selected z.selected_le
  · funext e
    exact congrArg z.selected
      (lpReplicaCurrentEdgeReflect_involutive G sites e)
  · exact lpReplicaProfileOrbitSlotMove_involutive G sites q z.slots


def lpReplicaPooledSelectedSlotMoveEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaPooledSelectedSlotState G sites q ≃
      LPReplicaPooledSelectedSlotState G sites q where
  toFun := lpReplicaPooledSelectedSlotMove G sites q
  invFun := lpReplicaPooledSelectedSlotMove G sites q
  left_inv := lpReplicaPooledSelectedSlotMove_involutive G sites q
  right_inv := lpReplicaPooledSelectedSlotMove_involutive G sites q



noncomputable def lpReplicaPooledSelectedSlotStateOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaPooledSelectedSlotState G sites q :=
  lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q
    ⟨⟨m, hm⟩,
      ⟨⟨StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P,
          StatMech.Sharpness.FluxEdgeCopy.profileFlux_le
            (lpReplicaCurrentGraph G sites) m P⟩,
        lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L⟩⟩

@[simp] theorem lpReplicaPooledSelectedSlotStateOfCopies_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L).profile = m := rfl

@[simp] theorem lpReplicaPooledSelectedSlotStateOfCopies_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L).selected =
        StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P := rfl



@[simp] theorem lpReplicaPooledSelectedSlotMove_ofCopies_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotMove G sites q
      (lpReplicaPooledSelectedSlotStateOfCopies
        G sites m q hm P L)).profile =
      lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P) := rfl



@[simp] theorem lpReplicaPooledSelectedSlotMove_ofCopies_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm
      (lpReplicaPooledSelectedSlotMove G sites q
        (lpReplicaPooledSelectedSlotStateOfCopies
          G sites m q hm P L))).2.2.1 =
      lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L := rfl

theorem lpReplicaPooledSelectedSlotMove_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective (lpReplicaPooledSelectedSlotMove G sites q) :=
  (lpReplicaPooledSelectedSlotMoveEquiv G sites q).injective




theorem card_image_lpReplicaPooledSelectedSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (LPReplicaPooledSelectedSlotState G sites q)) :
    (S.image (lpReplicaPooledSelectedSlotMove G sites q)).card = S.card := by
  classical
  exact Finset.card_image_of_injective S
    (lpReplicaPooledSelectedSlotMove_injective G sites q)



theorem lpReplicaPooledSelectedSlotMove_hall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (LPReplicaPooledSelectedSlotState G sites q)) :
    S.card <= (S.biUnion fun z =>
      {lpReplicaPooledSelectedSlotMove G sites q z}).card := by
  classical
  rw [Finset.biUnion_singleton]
  exact (card_image_lpReplicaPooledSelectedSlotMove G sites q S).ge

end

end StatMech.Ising
