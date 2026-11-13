/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarTopology
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.EulerFaces2
import Code.Lattice.EulerGeneral
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.JordanOuterFaceUnique
import Code.Lattice.BdEdgeMatchStarHull

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













def jcr_DualEulerCount (P : PlanarZ2Subgraph) : Prop :=
  Nat.card (regionGraph (imageGraph P)).ConnectedComponent = faceCount P.G









theorem jcr_dual_of_discreteJordan (P : PlanarZ2Subgraph)
    (h : DiscreteJordanSeparation P) : jcr_DualEulerCount P := by
  have hgeom : geometricRegionCount P = nullity P.G := geometricRegionCount_eq_nullity P h
  have hcard := geometricRegionCount_add_one_eq_card P
  rw [hgeom] at hcard
  unfold jcr_DualEulerCount
  rw [← hcard, faceCount]





theorem jcr_geometricRegionCount_eq_nullity_of_dual (P : PlanarZ2Subgraph)
    (h : jcr_DualEulerCount P) :
    geometricRegionCount P = nullity P.G := by
  have hcard := geometricRegionCount_add_one_eq_card P
  unfold jcr_DualEulerCount at h
  rw [h, faceCount] at hcard
  omega










theorem jcr_discreteJordan_of_dual (P : PlanarZ2Subgraph) (h : jcr_DualEulerCount P) :
    DiscreteJordanSeparation P := by
  have heq : geometricRegionCount P = nullity P.G :=
    jcr_geometricRegionCount_eq_nullity_of_dual P h
  unfold geometricRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩







theorem jcr_discreteJordan_iff_dualEulerCount (P : PlanarZ2Subgraph) :
    DiscreteJordanSeparation P ↔ jcr_DualEulerCount P :=
  ⟨jcr_dual_of_discreteJordan P, jcr_discreteJordan_of_dual P⟩








theorem jcr_faceCount_eq_geometric_regions_of_dual (P : PlanarZ2Subgraph)
    (h : jcr_DualEulerCount P) :
    faceCount P.G = geometricRegionCount P + 1 :=
  faceCount_eq_geometric_regions P (jcr_discreteJordan_of_dual P h)





theorem jcr_euler_geometric_regions_of_dual (P : PlanarZ2Subgraph)
    (h : jcr_DualEulerCount P) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1)
      = 1 + Nat.card P.G.ConnectedComponent :=
  euler_geometric_regions P (jcr_discreteJordan_of_dual P h)





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
    obtain ⟨w⟩ := pbs_reach_all x y
    refine ⟨w.transfer RG ?_⟩
    intro e he
    obtain ⟨a, b⟩ := e
    exact (jcr_regionGraph_adj_eq_lattice_of_bot hG a b).mpr (w.adj_of_mem_edges he)
  have hsub : Subsingleton RG.ConnectedComponent := by
    refine ⟨?_⟩
    refine ConnectedComponent.ind₂ ?_
    intro a b
    exact ConnectedComponent.sound (hreach a b)
  haveI : Nonempty RG.ConnectedComponent := ⟨RG.connectedComponentMk ![0, 0]⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨hsub, inferInstance⟩








theorem jcr_emptyGraph_dualEulerCount {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    jcr_DualEulerCount P := by
  unfold jcr_DualEulerCount
  rw [jcr_regionComponents_card_one_of_bot hG, hG]
  unfold faceCount nullity
  rw [SimpleGraph.edgeSet_bot]
  simp only [Set.ncard_empty, Nat.zero_add]
  rw [card_components_bot]
  omega





theorem jcr_discreteJordan_of_bot {P : PlanarZ2Subgraph} (hG : P.G = ⊥) :
    DiscreteJordanSeparation P :=
  jcr_discreteJordan_of_dual P (jcr_emptyGraph_dualEulerCount hG)

end Lattice

end StatMech
