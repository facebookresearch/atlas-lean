/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Foundations.ConfigSpace

open scoped BigOperators





set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech

namespace Lattice










inductive BoundaryCondition
  | free
  | wired
  | periodic
  deriving DecidableEq, Repr

namespace BoundaryCondition

instance : Inhabited BoundaryCondition := ⟨free⟩


theorem free_ne_wired : (free ≠ wired) := by decide

theorem free_ne_periodic : (free ≠ periodic) := by decide

theorem wired_ne_periodic : (wired ≠ periodic) := by decide

end BoundaryCondition

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]






def IsOpen (ω : Sym2 V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω s(x, y) = true

theorem isOpen_symm {ω : Sym2 V → Bool} {x y : V} (h : IsOpen G ω x y) :
    IsOpen G ω y x := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj.symm, ?_⟩
  rwa [Sym2.eq_swap]

theorem isOpen_irrefl {ω : Sym2 V → Bool} (x : V) : ¬ IsOpen G ω x x :=
  fun h => h.1.ne rfl

instance (ω : Sym2 V → Bool) : DecidableRel (IsOpen G ω) :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ ω s(x, y) = true))




def openGraph (ω : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := IsOpen G ω x y
  symm _ _ h := isOpen_symm G h
  loopless := ⟨fun x h => isOpen_irrefl G x h⟩

@[simp]
theorem openGraph_adj (ω : Sym2 V → Bool) (x y : V) :
    (openGraph G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true := Iff.rfl

instance (ω : Sym2 V → Bool) : DecidableRel (openGraph G ω).Adj :=
  fun x y => inferInstanceAs (Decidable (IsOpen G ω x y))



theorem openGraph_le (ω : Sym2 V → Bool) : openGraph G ω ≤ G := fun _ _ h => h.1



noncomputable def numClustersFree (ω : Sym2 V → Bool) : ℕ :=
  Nat.card (openGraph G ω).ConnectedComponent

theorem numClustersFree_eq_card (ω : Sym2 V → Bool) :
    numClustersFree G ω = Fintype.card (openGraph G ω).ConnectedComponent := by
  rw [numClustersFree, Nat.card_eq_fintype_card]



variable (bdry : V → Prop) [DecidablePred bdry]




def wireRel (x y : V) : Prop := bdry x ∧ bdry y

instance : DecidableRel (wireRel bdry) :=
  fun x y => inferInstanceAs (Decidable (bdry x ∧ bdry y))


def boundaryCliqueGraph : SimpleGraph V := SimpleGraph.fromRel (wireRel bdry)

@[simp]
theorem boundaryCliqueGraph_adj (x y : V) :
    (boundaryCliqueGraph bdry).Adj x y ↔ x ≠ y ∧ bdry x ∧ bdry y := by
  rw [boundaryCliqueGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (⟨hx, hy⟩ | ⟨hy, hx⟩)⟩ <;> exact ⟨hne, hx, hy⟩
  · rintro ⟨hne, hx, hy⟩
    exact ⟨hne, Or.inl ⟨hx, hy⟩⟩

instance : DecidableRel (boundaryCliqueGraph bdry).Adj :=
  fun x y => inferInstanceAs (Decidable ((SimpleGraph.fromRel (wireRel bdry)).Adj x y))





def wiredGraph (ω : Sym2 V → Bool) : SimpleGraph V :=
  openGraph G ω ⊔ boundaryCliqueGraph bdry

@[simp]
theorem wiredGraph_adj (ω : Sym2 V → Bool) (x y : V) :
    (wiredGraph G bdry ω).Adj x y ↔
      (G.Adj x y ∧ ω s(x, y) = true) ∨ (x ≠ y ∧ bdry x ∧ bdry y) := by
  rw [wiredGraph, SimpleGraph.sup_adj, openGraph_adj, boundaryCliqueGraph_adj]

instance (ω : Sym2 V → Bool) : DecidableRel (wiredGraph G bdry ω).Adj :=
  fun x y => inferInstanceAs (Decidable ((openGraph G ω ⊔ boundaryCliqueGraph bdry).Adj x y))


theorem openGraph_le_wiredGraph (ω : Sym2 V → Bool) :
    openGraph G ω ≤ wiredGraph G bdry ω := le_sup_left



theorem wiredGraph_adj_of_bdry {ω : Sym2 V → Bool} {x y : V}
    (hne : x ≠ y) (hx : bdry x) (hy : bdry y) :
    (wiredGraph G bdry ω).Adj x y := by
  rw [wiredGraph_adj]
  exact Or.inr ⟨hne, hx, hy⟩



noncomputable def numClustersWired (ω : Sym2 V → Bool) : ℕ :=
  Nat.card (wiredGraph G bdry ω).ConnectedComponent

theorem numClustersWired_eq_card (ω : Sym2 V → Bool) :
    numClustersWired G bdry ω
      = Fintype.card (wiredGraph G bdry ω).ConnectedComponent := by
  rw [numClustersWired, Nat.card_eq_fintype_card]





theorem numClustersWired_le_numClustersFree (ω : Sym2 V → Bool) :
    numClustersWired G bdry ω ≤ numClustersFree G ω :=
  SimpleGraph.ConnectedComponent.card_le_card_of_le (openGraph_le_wiredGraph G bdry ω)










noncomputable def numClusters (bc : BoundaryCondition) (ω : Sym2 V → Bool) : ℕ :=
  match bc with
  | BoundaryCondition.free => numClustersFree G ω
  | BoundaryCondition.wired => numClustersWired G bdry ω
  | BoundaryCondition.periodic => numClustersFree G ω

@[simp]
theorem numClusters_free (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.free ω = numClustersFree G ω := rfl

@[simp]
theorem numClusters_wired (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.wired ω = numClustersWired G bdry ω := rfl

@[simp]
theorem numClusters_periodic (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.periodic ω = numClustersFree G ω := rfl



theorem numClusters_wired_le_free (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.wired ω
      ≤ numClusters G bdry BoundaryCondition.free ω :=
  numClustersWired_le_numClustersFree G bdry ω

end Lattice

end StatMech
