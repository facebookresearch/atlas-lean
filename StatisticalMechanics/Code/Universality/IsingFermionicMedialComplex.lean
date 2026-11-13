/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicLocalSwitching
import Code.Universality.MedialTwoEdgeSwitch













open Finset SimpleGraph
open scoped BigOperators

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section


inductive FKIsingMedialSide
  | west | east | south | north
deriving DecidableEq, Fintype



def FKIsingMedialSide.angle : FKIsingMedialSide -> Real
  | .west => 0
  | .east => Real.pi
  | .south => -(Real.pi / 2)
  | .north => Real.pi / 2


abbrev FKIsingMedialVertex (P : PlanarZ2Subgraph) := P.G.edgeSet


abbrev FKIsingMedialDart (P : PlanarZ2Subgraph) :=
  FKIsingMedialVertex P × FKIsingMedialSide

namespace FKIsingMedialDart

variable {P : PlanarZ2Subgraph}


def localMate (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : FKIsingMedialDart P :=
  match omega d.1.1, d.2 with
  | false, .west => (d.1, .south)
  | false, .south => (d.1, .west)
  | false, .east => (d.1, .north)
  | false, .north => (d.1, .east)
  | true, .west => (d.1, .north)
  | true, .north => (d.1, .west)
  | true, .east => (d.1, .south)
  | true, .south => (d.1, .east)

theorem localMate_involutive (omega : ConfigSpace (Sym2 P.V)) :
    Function.Involutive (localMate omega) := by
  rintro ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;> simp [localMate, h]

theorem localMate_ne (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : localMate omega d ≠ d := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;> simp [localMate, h]

def localMateEquiv (omega : ConfigSpace (Sym2 P.V)) :
    FKIsingMedialDart P ≃ FKIsingMedialDart P where
  toFun := localMate omega
  invFun := localMate omega
  left_inv := localMate_involutive omega
  right_inv := localMate_involutive omega



theorem localMate_edgeFlip (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) (side : FKIsingMedialSide) :
    localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (e, side) =
      match omega e.1, side with
      | false, .west => (e, .north)
      | false, .north => (e, .west)
      | false, .east => (e, .south)
      | false, .south => (e, .east)
      | true, .west => (e, .south)
      | true, .south => (e, .west)
      | true, .east => (e, .north)
      | true, .north => (e, .east) := by
  cases h : omega e.1 <;> cases side <;>
    simp [localMate, FKIsingDobrushinDomain.localEdgeFlipEquiv,
      FKIsingDobrushinDomain.localEdgeFlip, h]


theorem localMate_edgeFlip_of_ne (omega : ConfigSpace (Sym2 P.V))
    (e f : FKIsingMedialVertex P) (hef : f ≠ e)
    (side : FKIsingMedialSide) :
    localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (f, side) =
      localMate omega (f, side) := by
  have hne : f.1 ≠ e.1 := by
    intro h
    exact hef (Subtype.ext h)
  cases h : omega f.1 <;> cases side <;>
    simp [localMate, FKIsingDobrushinDomain.localEdgeFlipEquiv,
      FKIsingDobrushinDomain.localEdgeFlip, Function.update_of_ne hne, h]

end FKIsingMedialDart




structure FKIsingDobrushinMedialComplex (P : PlanarZ2Subgraph) where
  bondMate : Equiv.Perm (FKIsingMedialDart P)
  bondMate_involutive : Function.Involutive bondMate
  bondMate_ne : forall d, bondMate d ≠ d
  bondMate_ne_localMate : forall omega d,
    bondMate d ≠ FKIsingMedialDart.localMate omega d
  wiredArc : P.V -> Prop
  markedA : P.V
  markedB : P.V
  markedA_mem : wiredArc markedA
  markedB_mem : wiredArc markedB
  sourceDart : FKIsingMedialDart P
  terminalDart : FKIsingMedialDart P
  medialPosition : FKIsingMedialDart P -> Complex
  baseWinding : ConfigSpace (Sym2 P.V) -> FKIsingMedialVertex P -> Real
  winding_terminal : forall omega,
    baseWinding omega terminalDart.1 + terminalDart.2.angle = 0

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)



def winding (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : Real :=
  C.baseWinding omega d.1 + d.2.angle

@[simp] theorem winding_west (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .west) = C.baseWinding omega e := by
  simp [winding, FKIsingMedialSide.angle]

theorem winding_east (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .east) = C.winding omega (e, .west) + Real.pi := by
  simp [winding, FKIsingMedialSide.angle]

theorem winding_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .south) =
      C.winding omega (e, .west) - Real.pi / 2 := by
  simp [winding, FKIsingMedialSide.angle]
  ring

theorem winding_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .north) =
      C.winding omega (e, .west) + Real.pi / 2 := by
  simp [winding, FKIsingMedialSide.angle]



def loopGraph (omega : ConfigSpace (Sym2 P.V)) :
    SimpleGraph (FKIsingMedialDart P) where
  Adj d e :=
    e = FKIsingMedialDart.localMate omega d ∨ e = C.bondMate d
  symm := by
    intro d e h
    rcases h with rfl | rfl
    · left
      rw [FKIsingMedialDart.localMate_involutive]
    · right
      exact (C.bondMate_involutive d).symm
  loopless := ⟨by
    intro d h
    rcases h with h | h
    · exact FKIsingMedialDart.localMate_ne omega d h.symm
    · exact C.bondMate_ne d h.symm⟩

noncomputable instance loopGraphDecidableAdj
    (omega : ConfigSpace (Sym2 P.V)) : DecidableRel (C.loopGraph omega).Adj :=
  Classical.decRel _

theorem loopGraph_neighborFinset (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) :
    (C.loopGraph omega).neighborFinset d =
      {FKIsingMedialDart.localMate omega d, C.bondMate d} := by
  ext e
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rfl

theorem loopGraph_degree_eq_two (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : (C.loopGraph omega).degree d = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    C.loopGraph_neighborFinset omega d]
  exact Finset.card_pair (C.bondMate_ne_localMate omega d).symm



def explorationFinset (omega : ConfigSpace (Sym2 P.V)) :
    Finset (FKIsingMedialDart P) :=
  Finset.univ.filter fun d => (C.loopGraph omega).Reachable C.sourceDart d

def exploration (omega : ConfigSpace (Sym2 P.V)) :
    List (FKIsingMedialDart P) :=
  (C.explorationFinset omega).toList

theorem mem_exploration_iff (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) :
    d ∈ C.exploration omega ↔
      (C.loopGraph omega).Reachable C.sourceDart d := by
  simp [exploration, explorationFinset]

theorem source_mem_exploration (omega : ConfigSpace (Sym2 P.V)) :
    C.sourceDart ∈ C.exploration omega := by
  rw [C.mem_exploration_iff]

theorem localMate_mem_exploration_iff
    (omega : ConfigSpace (Sym2 P.V)) (d : FKIsingMedialDart P) :
    FKIsingMedialDart.localMate omega d ∈ C.exploration omega ↔
      d ∈ C.exploration omega := by
  rw [C.mem_exploration_iff, C.mem_exploration_iff]
  have hadj : (C.loopGraph omega).Adj d
      (FKIsingMedialDart.localMate omega d) := Or.inl rfl
  exact ⟨fun h => h.trans hadj.symm.reachable,
    fun h => h.trans hadj.reachable⟩

theorem closed_west_mem_iff_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .west) ∈ C.exploration (setClosed e.1 omega) ↔
      (e, .south) ∈ C.exploration (setClosed e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setClosed e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem closed_east_mem_iff_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .east) ∈ C.exploration (setClosed e.1 omega) ↔
      (e, .north) ∈ C.exploration (setClosed e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setClosed e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem open_west_mem_iff_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .west) ∈ C.exploration (setOpen e.1 omega) ↔
      (e, .north) ∈ C.exploration (setOpen e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setOpen e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem open_east_mem_iff_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    (e, .east) ∈ C.exploration (setOpen e.1 omega) ↔
      (e, .south) ∈ C.exploration (setOpen e.1 omega) := by
  have h := C.localMate_mem_exploration_iff (setOpen e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm



theorem loopGraph_setOpen_eq_twoEdgeSwitch
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P) :
    C.loopGraph (setOpen e.1 omega) =
      medialTwoEdgeSwitch (C.loopGraph (setClosed e.1 omega))
        (e, .west) (e, .south) (e, .east) (e, .north) := by
  have hbW : C.bondMate (e, .west) ≠ (e, .south) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .west)
  have hbS : C.bondMate (e, .south) ≠ (e, .west) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .south)
  have hbE : C.bondMate (e, .east) ≠ (e, .north) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .east)
  have hbN : C.bondMate (e, .north) ≠ (e, .east) := by
    simpa [FKIsingMedialDart.localMate] using
      C.bondMate_ne_localMate (setClosed e.1 omega) (e, .north)
  have hbWr : (e, .south) ≠ C.bondMate (e, .west) := Ne.symm hbW
  have hbSr : (e, .west) ≠ C.bondMate (e, .south) := Ne.symm hbS
  have hbEr : (e, .north) ≠ C.bondMate (e, .east) := Ne.symm hbE
  have hbNr : (e, .east) ≠ C.bondMate (e, .north) := Ne.symm hbN
  have hlocal_of_ne (d : FKIsingMedialVertex P) (hd : d ≠ e)
      (side : FKIsingMedialSide) :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  ext d f
  rcases d with ⟨d, ds⟩
  rcases f with ⟨f, fs⟩
  by_cases hd : d = e <;> by_cases hf : f = e
  · subst d
    subst f
    cases ds <;> cases fs <;>
      simp [loopGraph, medialTwoEdgeSwitch, FKIsingMedialDart.localMate,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hbWr, hbNr, hbEr, hbSr]
  · subst d
    cases ds <;>
      simp [loopGraph, medialTwoEdgeSwitch, FKIsingMedialDart.localMate,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hf]
  · subst f
    have hlocal := hlocal_of_ne d hd ds
    cases fs <;>
      simp [loopGraph, medialTwoEdgeSwitch, hlocal,
        SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, hd]
  · have hlocal := hlocal_of_ne d hd ds
    have hold : s((d, ds), (f, fs)) ∉
        ({s((e, .west), (e, .south)), s((e, .east), (e, .north))} :
          Set (Sym2 (FKIsingMedialDart P))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor <;> intro h
      · rcases Sym2.eq_iff.mp h with h | h
        · exact hd (Prod.mk.inj h.1).1
        · exact hd (Prod.mk.inj h.1).1
      · rcases Sym2.eq_iff.mp h with h | h
        · exact hd (Prod.mk.inj h.1).1
        · exact hd (Prod.mk.inj h.1).1
    change ((f, fs) = FKIsingMedialDart.localMate (setOpen e.1 omega) (d, ds) ∨
        (f, fs) = C.bondMate (d, ds)) ↔ _
    rw [medialTwoEdgeSwitch, SimpleGraph.sup_adj, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj]
    simp only [loopGraph]
    rw [hlocal]
    simp [hold, SimpleGraph.edge_adj, hd, hf]




theorem open_local_mem_of_closed_west_mem_not_east
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (hwest : (e, .west) ∈ C.exploration (setClosed e.1 omega))
    (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceWest : G.Reachable C.sourceDart (e, .west) :=
    (C.mem_exploration_iff _ _).1 hwest
  have hwestEast : ¬ G.Reachable (e, .west) (e, .east) := by
    intro h
    exact heast ((C.mem_exploration_iff _ _).2 (hsourceWest.trans h))
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heven : forall d, Even (G.degree d) := by
    intro d
    rw [C.loopGraph_degree_eq_two]
    exact even_two
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G heven
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← C.loopGraph_setOpen_eq_twoEdgeSwitch omega e] at hall
  intro side
  rw [C.mem_exploration_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2



theorem open_local_mem_of_closed_east_mem_not_west
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (heast : (e, .east) ∈ C.exploration (setClosed e.1 omega))
    (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceEast : G.Reachable C.sourceDart (e, .east) :=
    (C.mem_exploration_iff _ _).1 heast
  have hwestEast : ¬ G.Reachable (e, .west) (e, .east) := by
    intro h
    exact hwest ((C.mem_exploration_iff _ _).2
      (hsourceEast.trans h.symm))
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heven : forall d, Even (G.degree d) := by
    intro d
    rw [C.loopGraph_degree_eq_two]
    exact even_two
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G heven
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← C.loopGraph_setOpen_eq_twoEdgeSwitch omega e] at hall
  intro side
  rw [C.mem_exploration_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2



theorem open_local_not_mem_of_closed_west_east_not_mem
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P)
    (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega))
    (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
    forall side, (e, side) ∉ C.exploration (setOpen e.1 omega) := by
  let G := C.loopGraph (setClosed e.1 omega)
  have hsourceWest : ¬ G.Reachable C.sourceDart (e, .west) := by
    simpa only [G, ← C.mem_exploration_iff] using hwest
  have hsourceEast : ¬ G.Reachable C.sourceDart (e, .east) := by
    simpa only [G, ← C.mem_exploration_iff] using heast
  have hwestSouth : G.Adj (e, .west) (e, .south) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have heastNorth : G.Adj (e, .east) (e, .north) := by
    exact Or.inl (by simp [FKIsingMedialDart.localMate])
  have hiff (d : FKIsingMedialDart P) :
      (C.loopGraph (setOpen e.1 omega)).Reachable C.sourceDart d ↔
        G.Reachable C.sourceDart d := by
    rw [C.loopGraph_setOpen_eq_twoEdgeSwitch omega e]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G hwestSouth
      heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach := (C.mem_exploration_iff _ _).1 hopen
  have hclosed : (e, side) ∈ C.exploration (setClosed e.1 omega) :=
    (C.mem_exploration_iff _ _).2 ((hiff (e, side)).1 hopenReach)
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · exact hwest ((C.closed_west_mem_iff_south omega e).2 hclosed)
  · exact heast ((C.closed_east_mem_iff_north omega e).2 hclosed)






theorem local_switch_membership_classification
    (omega : ConfigSpace (Sym2 P.V)) (e : FKIsingMedialVertex P) :
    ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∉ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∈ C.exploration (setClosed e.1 omega) ∧
        forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨
      ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧
        (e, .east) ∈ C.exploration (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (e, .west) ∈ C.exploration (setClosed e.1 omega)
  · by_cases heast : (e, .east) ∈ C.exploration (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        C.open_local_mem_of_closed_west_mem_not_east omega e hwest heast⟩)
  · by_cases heast : (e, .east) ∈ C.exploration (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        C.open_local_mem_of_closed_east_mem_not_west omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        C.open_local_not_mem_of_closed_west_east_not_mem omega e hwest heast⟩


def localDarts (e : FKIsingMedialVertex P) : Fin 4 -> FKIsingMedialDart P
  | 0 => (e, .west)
  | 1 => (e, .east)
  | 2 => (e, .south)
  | 3 => (e, .north)



def toDobrushinDomain
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart) :
    FKIsingDobrushinDomain P (FKIsingMedialDart P) where
  wiredArc := C.wiredArc
  markedA := C.markedA
  markedB := C.markedB
  markedA_mem := C.markedA_mem
  markedB_mem := C.markedB_mem
  sourceEdge := C.sourceDart
  terminalEdge := C.terminalDart
  medialPosition := C.medialPosition
  exploration := C.exploration
  source_mem := C.source_mem_exploration
  terminal_mem := fun omega => (C.mem_exploration_iff omega C.terminalDart).2
    (hterminal omega)
  winding := C.winding
  winding_terminal := C.winding_terminal



def caseTwoExplorationSwitchingLaw
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart)
    (a b : P.V) (hab : P.G.Adj a b)
    (hclosedWest : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .west) ∈ C.exploration (setClosed e.1 omega))
    (hclosedEast : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .east) ∉ C.exploration (setClosed e.1 omega))
    (hseparated : forall omega,
      ¬(openSub P.G (setClosed s(a, b) omega) ⊔
        (C.toDobrushinDomain hterminal).wiring).Reachable a b)
    (hbalance : (C.toDobrushinDomain hterminal).ClosedOpenPairedBalance
      s(a, b) (localDarts
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩)) :
    (C.toDobrushinDomain hterminal).CaseTwoExplorationSwitchingLaw where
  crossingA := a
  crossingB := b
  crossing_adj := hab
  edges := localDarts
    ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
  closed_endpoints_not_reachable := hseparated
  closed_mem_zero := hclosedWest
  closed_not_mem_one := hclosedEast
  closed_mem_two := by
    intro omega
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    exact (C.closed_west_mem_iff_south omega e).1 (hclosedWest omega)
  closed_not_mem_three := by
    intro omega hnorth
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    exact hclosedEast omega
      ((C.closed_east_mem_iff_north omega e).2 hnorth)
  open_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    have hall := C.open_local_mem_of_closed_west_mem_not_east omega e
      (hclosedWest omega) (hclosedEast omega)
    fin_cases k
    · exact hall .west
    · exact hall .east
    · exact hall .south
    · exact hall .north
  paired_balance := hbalance



def caseOneExplorationSwitchingLaw
    (hterminal : forall omega,
      (C.loopGraph omega).Reachable C.sourceDart C.terminalDart)
    (a b : P.V) (hab : P.G.Adj a b)
    (hclosedWest : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .west) ∉ C.exploration (setClosed e.1 omega))
    (hclosedEast : forall omega,
      let e : FKIsingMedialVertex P :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
      (e, .east) ∉ C.exploration (setClosed e.1 omega))
    :
    (C.toDobrushinDomain hterminal).CaseOneExplorationSwitchingLaw where
  crossingA := a
  crossingB := b
  crossing_adj := hab
  edges := localDarts
    ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
  closed_not_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    fin_cases k
    · exact hclosedWest omega
    · exact hclosedEast omega
    · intro hsouth
      exact hclosedWest omega ((C.closed_west_mem_iff_south omega e).2 hsouth)
    · intro hnorth
      exact hclosedEast omega ((C.closed_east_mem_iff_north omega e).2 hnorth)
  open_not_mem := by
    intro omega k
    let e : FKIsingMedialVertex P :=
      ⟨s(a, b), (SimpleGraph.mem_edgeSet P.G).2 hab⟩
    have hall := C.open_local_not_mem_of_closed_west_east_not_mem omega e
      (hclosedWest omega) (hclosedEast omega)
    fin_cases k
    · exact hall .west
    · exact hall .east
    · exact hall .south
    · exact hall .north

end FKIsingDobrushinMedialComplex

end

end StatMech.Universality
