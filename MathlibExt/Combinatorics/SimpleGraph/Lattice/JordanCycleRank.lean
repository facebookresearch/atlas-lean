/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique

/-!
# Finiteness of the components of the region graph

For a `PlanarZ2Subgraph` `P` the region graph `regionGraph (imageGraph P)` has finitely many
components; for a graph without edges it is the whole lattice and has one component. The region
graph removes the quarter turns `crossEdge e` of the edges of `P`, not the crossing dual edges, so
its components do not count the faces of `P` (for the unit square it is connected while the face
count is two). The faithful face count is `StatMech.Lattice.jed_faithfulDiscreteJordan`.

## Main results

* `StatMech.Lattice.jcr_regionComponents_finite`: the region graph has finitely many components.
* `StatMech.Lattice.jcr_regionComponents_card_one_of_bot`: for a graph without edges it has one
  component.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

theorem jcr_regionComponents_finite (P : PlanarZ2Subgraph) :
    Finite (regionGraph (imageGraph P)).ConnectedComponent := by
  classical
  set R := outerBoxRadius P with hR
  set RG := regionGraph (imageGraph P) with hRG
  set S : Set (Site 2) := box 2 R ∪ {beacon 2 R} with hS
  have hSfin : S.Finite := (box_finite 2 R).union (Set.finite_singleton _)
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 R
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hxbox
    have hmk : RG.connectedComponentMk x = outerRegion P := exterior_in_outerRegion P hxext
    refine ⟨beacon 2 R, Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 R) = c
    have hbeac : RG.connectedComponentMk (beacon 2 R) = outerRegion P := rfl
    rw [hbeac, ← hmk]
    exact hx

attribute [instance] jcr_regionComponents_finite

theorem jcr_imageGraph_bot_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    imageGraph P = ⊥ := by
  ext a b
  simp only [imageGraph_adj, SimpleGraph.bot_adj, iff_false]
  rintro ⟨x, y, hadj, _, _⟩
  rw [hG] at hadj
  exact (SimpleGraph.bot_adj _ _).mp hadj

theorem jcr_regionGraph_adj_eq_lattice_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥)
    (f g : Site 2) :
    (regionGraph (imageGraph P)).Adj f g ↔ (hypercubicLattice 2).Adj f g := by
  rw [regionGraph_adj, jcr_imageGraph_bot_of_bot hG, SimpleGraph.edgeSet_bot]
  simp

theorem jcr_regionComponents_card_one_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    Nat.card (regionGraph (imageGraph P)).ConnectedComponent = 1 := by
  classical
  set RG := regionGraph (imageGraph P) with hRG
  have hreach : ∀ x y : Site 2, RG.Reachable x y := by
    intro x y
    obtain ⟨w⟩ := hypercubicLattice_two_reachable x y
    refine ⟨w.transfer RG ?_⟩
    intro e he
    obtain ⟨a, b⟩ := e
    exact (jcr_regionGraph_adj_eq_lattice_of_bot hG a b).mpr (w.adj_of_mem_edges he)
  have hsub : Subsingleton RG.ConnectedComponent := by
    refine ⟨?_⟩
    refine ConnectedComponent.ind₂ ?_
    intro a b
    exact ConnectedComponent.sound (hreach a b)
  have : Nonempty RG.ConnectedComponent := ⟨RG.connectedComponentMk ![0, 0]⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨hsub, inferInstance⟩

end Lattice

end StatMech
