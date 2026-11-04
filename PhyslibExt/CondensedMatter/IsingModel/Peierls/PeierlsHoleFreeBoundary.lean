/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TreeNoSepEuler
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.DualCircuitDecoding

/-!
# The contour of a hole-free planar set is a single cycle

If a finite set `K ⊆ ℤ²` and its complement are both connected after removing the edges between
them, its face-boundary graph is connected and 2-regular on its support, a single cycle.

## i. Overview

Shifting every site by `(-1, -1)` identifies the lattice with the barrier edges of `K` removed
with the face region graph of the face-boundary graph: the dual of the dual is the primal
lattice. Under the hypothesis that `K` and its complement are each connected in the lattice minus
the barrier, the face region graph has exactly two components. The face-boundary graph is a
finite planar subgraph of `ℤ²` with all degrees at least two, and Euler's formula for planar
graphs then forces it to be connected with cycle rank one, hence a single cycle in which every
face has degree exactly two.

## ii. Key results

- `phb_doubleDualIso` : the lattice minus the barrier of `K` is isomorphic to the face region
  graph of the face-boundary graph.
- `faceBoundaryConnected_of_connected_complement` : the contour of a hole-free set is connected.
- `faceBoundaryGraph_degree_eq_two_of_connected_complement` : every contour face has degree two.
- `phb_planarBoundary_isCycles_of_connected_complement` : the contour is a disjoint union of
  cycles, here a single one.

## iii. Table of contents

- A. The double dual of the square lattice
- B. The contour as a planar subgraph
- C. Hole-free sets have a single contour cycle

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

/-! ## A. The double dual of the square lattice -/

/-- The shift `x ↦ x - (1, 1)` identifying the dual of the dual lattice with `ℤ²`. -/
def phb_doubleDualShift (x : Site 2) : Site 2 := ![x 0 - 1, x 1 - 1]

/-- The shift by `(-1, -1)` as an equivalence of `ℤ²`. -/
def phb_doubleDualEquiv : Site 2 ≃ Site 2 where
  toFun := phb_doubleDualShift
  invFun x := ![x 0 + 1, x 1 + 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp [phb_doubleDualShift]
  right_inv x := by
    funext i
    fin_cases i <;> simp [phb_doubleDualShift]

lemma phb_doubleDualShift_latAdj {x y : Site 2} :
    (hypercubicLattice 2).Adj (phb_doubleDualShift x) (phb_doubleDualShift y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, phb_doubleDualShift,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

lemma phb_sharedPrimalEdge_shift_eq_flankFaces {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    sharedPrimalEdge (phb_doubleDualShift x) (phb_doubleDualShift y) = flankFaces x y := by
  classical
  have hshift : (hypercubicLattice 2).Adj (phb_doubleDualShift x) (phb_doubleDualShift y) :=
    phb_doubleDualShift_latAdj.mpr hxy
  rw [← symPrimal_eq_shared hshift]
  rcases adj_cases hxy with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold symPrimal flankFaces phb_doubleDualShift
    rw [ite_eq_left (show (![x 0 - 1, x 1 - 1] : Site 2) 0 = ![y 0 - 1, y 1 - 1] 0 by simp [h0]),
      ite_eq_left h0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hy with hxy | hyx
    · rw [show max (x 1 - 1) (y 1 - 1) = y 1 by omega,
          show min (x 1) (y 1) = y 1 by omega]
      congr 1; ext i; fin_cases i <;> simp
    · rw [show max (x 1 - 1) (y 1 - 1) = x 1 by omega,
          show min (x 1) (y 1) = x 1 by omega]
      congr 1; ext i; fin_cases i <;> simp
  · unfold symPrimal flankFaces phb_doubleDualShift
    rw [ite_eq_right
        (show ¬ (![x 0 - 1, x 1 - 1] : Site 2) 0 = ![y 0 - 1, y 1 - 1] 0 by simp; omega),
      ite_eq_right (show ¬ x 0 = y 0 by omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases hx with hxy | hyx
    · rw [show max (x 0 - 1) (y 0 - 1) = y 0 by omega,
          show min (x 0) (y 0) = y 0 by omega, h1, min_self]
      congr 1 <;> ext i <;> fin_cases i <;> simp
    · rw [show max (x 0 - 1) (y 0 - 1) = x 0 by omega,
          show min (x 0) (y 0) = x 0 by omega, h1, min_self]
      congr 1 <;> ext i <;> fin_cases i <;> simp

lemma phb_flankFaces_mem_faceBoundaryGraph_iff {K : Set (Site 2)} {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    flankFaces x y ∈ (faceBoundaryGraph K).edgeSet ↔ bdEdge K s(x, y) := by
  constructor
  · intro h
    have him := symPrimalSym_mem_boundaryEdgeSet h
    rw [symPrimalSym_flankFaces hxy] at him
    rw [bdEdge_eq_edgeStraddles, edgeStraddles_iff_mem_boundaryEdgeSet K hxy]
    exact him
  · intro h
    have hmem : s(x, y) ∈ boundaryEdgeSet K := by
      rw [← edgeStraddles_iff_mem_boundaryEdgeSet K hxy, ← bdEdge_eq_edgeStraddles]
      exact h
    exact (flankFacesSym_mem_edgeSet hmem).1

/-- The lattice minus the barrier edges of `K` is isomorphic, by the shift by `(-1, -1)`, to the
face region graph of the face-boundary graph of `K`. -/
noncomputable def phb_doubleDualIso (K : Set (Site 2)) :
    latticeMinusBarrier K ≃g whb_faceRegion (faceBoundaryGraph K) where
  toEquiv := phb_doubleDualEquiv
  map_rel_iff' := by
    intro x y
    change (whb_faceRegion (faceBoundaryGraph K)).Adj
        (phb_doubleDualShift x) (phb_doubleDualShift y) ↔
      (latticeMinusBarrier K).Adj x y
    rw [latticeMinusBarrier_adj, whb_faceRegion_adj]
    have hadj := phb_doubleDualShift_latAdj (x := x) (y := y)
    constructor
    · rintro ⟨hshift, hmem⟩
      have hxy := hadj.mp hshift
      refine ⟨hxy, ?_⟩
      rw [← phb_flankFaces_mem_faceBoundaryGraph_iff hxy,
        ← phb_sharedPrimalEdge_shift_eq_flankFaces hxy]
      exact hmem
    · rintro ⟨hxy, hbd⟩
      refine ⟨hadj.mpr hxy, ?_⟩
      rw [phb_sharedPrimalEdge_shift_eq_flankFaces hxy,
        phb_flankFaces_mem_faceBoundaryGraph_iff hxy]
      exact hbd

lemma phb_doubleDual_component_card (K : Set (Site 2)) :
    Nat.card (whb_faceRegion (faceBoundaryGraph K)).ConnectedComponent =
      Nat.card (latticeMinusBarrier K).ConnectedComponent := by
  exact Nat.card_congr (phb_doubleDualIso K).connectedComponentEquiv.symm

/-! ## B. The contour as a planar subgraph -/

lemma phb_faceBoundaryGraph_support_finite (K : Set (Site 2)) (hK : K.Finite) :
    (faceBoundaryGraph K).support.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph K hK
  exact T.finite_toSet.subset hT

/-- The support of the face-boundary graph of a finite set `K`, as a finset. -/
noncomputable def phb_boundarySupport (K : Set (Site 2)) (hK : K.Finite) : Finset (Site 2) :=
  (phb_faceBoundaryGraph_support_finite K hK).toFinset

@[simp] lemma phb_mem_boundarySupport_iff (K : Set (Site 2)) (hK : K.Finite) (f : Site 2) :
    f ∈ phb_boundarySupport K hK ↔ f ∈ (faceBoundaryGraph K).support := by
  simp [phb_boundarySupport]

/-- The face-boundary graph of a finite set `K`, as a finite planar subgraph of `ℤ²`. -/
noncomputable def phb_planarBoundary (K : Set (Site 2)) (hK : K.Finite) :
    PlanarZ2Subgraph where
  V := (faceBoundaryGraph K).support
  finV := (phb_faceBoundaryGraph_support_finite K hK).to_subtype
  decV := Classical.decEq _
  G := (faceBoundaryGraph K).induce (faceBoundaryGraph K).support
  emb := Function.Embedding.subtype _
  isSub := by
    intro x y hxy
    exact faceBoundaryGraph_le K hxy

lemma phb_imageGraph_planarBoundary (K : Set (Site 2)) (hK : K.Finite) :
    imageGraph (phb_planarBoundary K hK) = faceBoundaryGraph K := by
  ext a b
  rw [imageGraph_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact hxy
  · intro hab
    exact ⟨⟨a, hab.mem_support_left⟩, ⟨b, hab.mem_support_right⟩, hab, rfl, rfl⟩

lemma phb_two_le_degree_planarBoundary (K : Set (Site 2)) (hK : K.Finite)
    [Fintype (phb_planarBoundary K hK).V]
    [DecidableRel (phb_planarBoundary K hK).G.Adj]
    (v : (phb_planarBoundary K hK).V) :
    2 ≤ (phb_planarBoundary K hK).G.degree v := by
  classical
  let e : ↑((phb_planarBoundary K hK).G.neighborSet v) ≃
      ↑((faceBoundaryGraph K).neighborSet v.val) :=
    { toFun := fun z => ⟨z.val.val, z.property⟩
      invFun := fun z => ⟨⟨z.val, z.property.mem_support_right⟩, z.property⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun z => by ext; rfl }
  have hdeg : (phb_planarBoundary K hK).G.degree v =
      (faceBoundaryGraph K).degree v.val := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  have hpos : 0 < (phb_planarBoundary K hK).G.degree v := by
    rw [hdeg]
    exact ((faceBoundaryGraph K).degree_pos_iff_mem_support v.val).2 v.property
  have heven : Even ((phb_planarBoundary K hK).G.degree v) := by
    rw [hdeg]
    exact degree_faceBoundaryGraph_even K v.val
  obtain ⟨d, hd⟩ := heven
  omega

lemma phb_card_vertices_le_edges (K : Set (Site 2)) (hK : K.Finite) :
    Nat.card (phb_planarBoundary K hK).V ≤
      (phb_planarBoundary K hK).G.edgeSet.ncard := by
  classical
  let := Fintype.ofFinite (phb_planarBoundary K hK).V
  let : DecidableRel (phb_planarBoundary K hK).G.Adj := Classical.decRel _
  have hlower : 2 * Fintype.card (phb_planarBoundary K hK).V ≤
      ∑ v : (phb_planarBoundary K hK).V, (phb_planarBoundary K hK).G.degree v := by
    calc
      2 * Fintype.card (phb_planarBoundary K hK).V =
          ∑ _v : (phb_planarBoundary K hK).V, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : (phb_planarBoundary K hK).V,
          (phb_planarBoundary K hK).G.degree v :=
        Finset.sum_le_sum fun v _ => phb_two_le_degree_planarBoundary K hK v
  have hhand := (phb_planarBoundary K hK).G.sum_degrees_eq_twice_card_edges
  have hedge : (phb_planarBoundary K hK).G.edgeSet.ncard =
      (phb_planarBoundary K hK).G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hhand, ← hedge] at hlower
  rw [Nat.card_eq_fintype_card]
  omega

/-! ## C. Hole-free sets have a single contour cycle -/

lemma faceBoundaryConnected_of_connected_complement
    (K : Set (Site 2)) (hK : K.Finite) {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
    FaceBoundaryConnected K (phb_boundarySupport K hK) := by
  classical
  let P := phb_planarBoundary K hK
  have htwoCut : Nat.card (latticeMinusBarrier K).ConnectedComponent = 2 :=
    jcs_two_components_of_sides K hx hy hin hout
  have htwoDual : Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = 2 := by
    rw [show imageGraph P = faceBoundaryGraph K from phb_imageGraph_planarBoundary K hK,
      phb_doubleDual_component_card K]
    exact htwoCut
  have hbounded : whc_faithfulRegionCount P = 1 := by
    have hcount := jfc_whb_bounded_add_one_eq_card P
    rw [htwoDual] at hcount
    omega
  have hnull : nullity P.G = 1 := by
    obtain ⟨e⟩ := jed_faithfulDiscreteJordan P
    have hcard := Nat.card_congr e
    have heq : whc_faithfulRegionCount P = nullity P.G := by
      simpa [whc_faithfulRegionCount] using hcard
    rw [← heq]
    exact hbounded
  have hVnonempty : Nonempty P.V := by
    obtain ⟨w⟩ := hypercubicLattice_two_reachable x y
    obtain ⟨u, v, huv⟩ := walk_mem_edgeBoundary K w hx hy
    obtain ⟨f, g, hfg⟩ := exists_faceBoundaryGraph_adj_of_edgeBoundary K huv
    exact ⟨⟨f, hfg.mem_support_left⟩⟩
  have hcomp : Nat.card P.G.ConnectedComponent = 1 := by
    have heuler := ecc_comp_add_edges_eq_card_add_nullity P.G
    have hedge := phb_card_vertices_le_edges K hK
    change Nat.card P.V ≤ P.G.edgeSet.ncard at hedge
    rw [hnull] at heuler
    have hpos : 0 < Nat.card P.G.ConnectedComponent := by
      let : Nonempty P.V := hVnonempty
      let : Nonempty P.G.ConnectedComponent := ⟨P.G.connectedComponentMk (Classical.arbitrary P.V)⟩
      exact Nat.card_pos
    omega
  have hconn : P.G.Connected := tnse_connected_of_card_components_eq_one hcomp
  change ((faceBoundaryGraph K).induce
    (↑(phb_boundarySupport K hK) : Set (Site 2))).Connected
  have hs : (↑(phb_boundarySupport K hK) : Set (Site 2)) =
      (faceBoundaryGraph K).support := by
    ext f
    simp
  rw [hs]
  simpa [P, phb_planarBoundary] using hconn

lemma phb_boundary_nullity_one_of_connected_complement
    (K : Set (Site 2)) (hK : K.Finite) {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
    nullity (phb_planarBoundary K hK).G = 1 := by
  let P := phb_planarBoundary K hK
  have htwoCut : Nat.card (latticeMinusBarrier K).ConnectedComponent = 2 :=
    jcs_two_components_of_sides K hx hy hin hout
  have htwoDual : Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = 2 := by
    rw [show imageGraph P = faceBoundaryGraph K from phb_imageGraph_planarBoundary K hK,
      phb_doubleDual_component_card K]
    exact htwoCut
  have hbounded : whc_faithfulRegionCount P = 1 := by
    have hcount := jfc_whb_bounded_add_one_eq_card P
    rw [htwoDual] at hcount
    omega
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan P
  have hcard := Nat.card_congr e
  have heq : whc_faithfulRegionCount P = nullity P.G := by
    simpa [whc_faithfulRegionCount] using hcard
  rw [← heq]
  exact hbounded

lemma faceBoundaryGraph_degree_eq_two_of_connected_complement
    (K : Set (Site 2)) (hK : K.Finite) {x y f : Site 2} (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b)
    (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 := by
  classical
  let P := phb_planarBoundary K hK
  let : Fintype P.V := Fintype.ofFinite P.V
  let : DecidableRel P.G.Adj := Classical.decRel _
  have hconnExact := faceBoundaryConnected_of_connected_complement K hK hx hy hin hout
  have hconn : P.G.Connected := by
    have hs : (↑(phb_boundarySupport K hK) : Set (Site 2)) =
        (faceBoundaryGraph K).support := by
      ext z
      simp
    rw [FaceBoundaryConnected, hs] at hconnExact
    simpa [P, phb_planarBoundary] using hconnExact
  have hnull : nullity P.G = 1 :=
    phb_boundary_nullity_one_of_connected_complement K hK hx hy hin hout
  have heuler := ecc_comp_add_edges_eq_card_add_nullity P.G
  have hcomp : Nat.card P.G.ConnectedComponent = 1 :=
    card_components_eq_one_of_connected hconn
  have hedge : P.G.edgeFinset.card = Fintype.card P.V := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at heuler
    rw [hcomp, hnull, Nat.card_eq_fintype_card] at heuler
    omega
  have hsum : ∑ v : P.V, P.G.degree v = 2 * Fintype.card P.V := by
    rw [P.G.sum_degrees_eq_twice_card_edges, hedge]
  let vf : P.V := ⟨f, hf⟩
  have hvdeg : P.G.degree vf = 2 := by
    have hlow : ∀ v : P.V, 2 ≤ P.G.degree v :=
      phb_two_le_degree_planarBoundary K hK
    have hrest : 2 * (Finset.univ.erase vf).card ≤
        ∑ v ∈ Finset.univ.erase vf, P.G.degree v := by
      calc
        2 * (Finset.univ.erase vf).card =
            ∑ _v ∈ Finset.univ.erase vf, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ Finset.univ.erase vf, P.G.degree v :=
          Finset.sum_le_sum fun v _ => hlow v
    have herase : (Finset.univ.erase vf).card + 1 = Fintype.card P.V := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ vf), Finset.card_univ]
      exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨vf⟩)
    have hsplit : (∑ v : P.V, P.G.degree v) =
        (∑ v ∈ Finset.univ.erase vf, P.G.degree v) + P.G.degree vf := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ vf)]
    have hvlow := hlow vf
    omega
  let e : ↑(P.G.neighborSet vf) ≃ ↑((faceBoundaryGraph K).neighborSet f) :=
    { toFun := fun z => ⟨z.val.val, z.property⟩
      invFun := fun z => ⟨⟨z.val, z.property.mem_support_right⟩, z.property⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun z => by ext; rfl }
  calc
    (faceBoundaryGraph K).degree f = Fintype.card ↑((faceBoundaryGraph K).neighborSet f) := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
    _ = Fintype.card ↑(P.G.neighborSet vf) := (Fintype.card_congr e).symm
    _ = P.G.degree vf := SimpleGraph.card_neighborSet_eq_degree P.G vf
    _ = 2 := hvdeg

lemma phb_planarBoundary_isCycles_of_connected_complement
    (K : Set (Site 2)) (hK : K.Finite) {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
    (phb_planarBoundary K hK).G.IsCycles := by
  classical
  let P := phb_planarBoundary K hK
  let : Fintype P.V := Fintype.ofFinite P.V
  let : DecidableRel P.G.Adj := Classical.decRel _
  intro v hv
  have hdeg : P.G.degree v = (faceBoundaryGraph K).degree v.val := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborSet_eq_degree]
    let e : ↑(P.G.neighborSet v) ≃ ↑((faceBoundaryGraph K).neighborSet v.val) :=
      { toFun := fun z => ⟨z.val.val, z.property⟩
        invFun := fun z => ⟨⟨z.val, z.property.mem_support_right⟩, z.property⟩
        left_inv := fun z => by ext; rfl
        right_inv := fun z => by ext; rfl }
    exact Fintype.card_congr e
  change (P.G.neighborSet v).ncard = 2
  calc
    (P.G.neighborSet v).ncard = Nat.card ↑(P.G.neighborSet v) :=
      (Nat.card_coe_set_eq _).symm
    _ = Fintype.card ↑(P.G.neighborSet v) := by rw [Nat.card_eq_fintype_card]
    _ = P.G.degree v := SimpleGraph.card_neighborSet_eq_degree P.G v
    _ = (faceBoundaryGraph K).degree v.val := hdeg
    _ = 2 := faceBoundaryGraph_degree_eq_two_of_connected_complement
      K hK hx hy hin hout v.property

end Lattice

end StatMech
