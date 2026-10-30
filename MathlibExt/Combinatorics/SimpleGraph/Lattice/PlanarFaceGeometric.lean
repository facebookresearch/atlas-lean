/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent

/-!
# Finite subgraphs of `ℤ²` and the regions of a rotated dual

A `PlanarZ2Subgraph` is a finite graph embedded in the square lattice. This file defines its region
graph, the square lattice with the edges `crossEdge e` removed for every edge `e` of the image, and
the number of finite components of the region graph.

`crossEdge` rotates an edge about the origin; it is not the dual edge crossing `e` in the
lower-left-corner labelling of faces, so the region graph does not count faces (for the unit
square it is connected). The faithful count, with the dual edge `sharedPrimalEdge`, is
`StatMech.Lattice.whc_FaithfulDiscreteJordan`, proved for all `PlanarZ2Subgraph`s in
`StatMech.Lattice.jed_faithfulDiscreteJordan`.

## Main definitions

* `StatMech.Lattice.PlanarZ2Subgraph`: a finite graph with an embedding into `ℤ²` mapping edges to
  lattice edges.
* `StatMech.Lattice.imageGraph P`: the image of `P` as a subgraph of `ℤ²`.
* `StatMech.Lattice.regionGraph G`: the square lattice with the rotated edges of `G` removed.
* `StatMech.Lattice.geometricRegionCount P`: the number of finite components of `regionGraph
  (imageGraph P)`.

## Main results

* `StatMech.Lattice.exists_infinite_region`: the region graph has an infinite component.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.Lattice

/-- The square lattice with the edge `crossEdge e` removed for every edge `e` of `G`. Since
`crossEdge` is a global rotation, this is not the faithful dual complement; see
`StatMech.Lattice.whb_faceRegion` for the version using `sharedPrimalEdge`. -/
def regionGraph (G : SimpleGraph (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet
  symm := by
    refine ⟨?_⟩
    intro f g ⟨hadj, hcross⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem regionGraph_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (regionGraph G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet := Iff.rfl

theorem regionGraph_le_dual (G : SimpleGraph (Site 2)) :
    regionGraph G ≤ hypercubicLattice 2 := fun _ _ h => h.1

/-- A finite graph together with an injective map into `ℤ²` that sends edges to lattice edges. -/
structure PlanarZ2Subgraph where
  /-- The vertex type. -/
  V : Type
  /-- The vertex type is finite. -/
  finV : Finite V
  /-- Equality of vertices is decidable. -/
  decV : DecidableEq V
  /-- The abstract graph. -/
  G : SimpleGraph V
  /-- The embedding of the vertices into `ℤ²`. -/
  emb : V ↪ Site 2
  /-- Edges are mapped to lattice edges. -/
  isSub : ∀ ⦃x y : V⦄, G.Adj x y → (hypercubicLattice 2).Adj (emb x) (emb y)

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV

/-- The image of a `PlanarZ2Subgraph` as a subgraph of the square lattice. -/
noncomputable def imageGraph (P : PlanarZ2Subgraph) : SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := by
    refine ⟨?_⟩
    rintro a b ⟨x, y, hadj, rfl, rfl⟩
    exact ⟨y, x, hadj.symm, rfl, rfl⟩
  loopless := ⟨by
    rintro a ⟨x, y, hadj, hx, hy⟩
    have : x = y := P.emb.injective (hx.trans hy.symm)
    exact P.G.irrefl (this ▸ hadj)⟩

@[simp] theorem imageGraph_adj (P : PlanarZ2Subgraph) (a b : Site 2) :
    (imageGraph P).Adj a b ↔ ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b :=
  Iff.rfl

theorem imageGraph_le_lattice (P : PlanarZ2Subgraph) :
    imageGraph P ≤ hypercubicLattice 2 := by
  rintro a b ⟨x, y, hadj, rfl, rfl⟩
  exact P.isSub hadj

/-- The number of finite connected components of the region graph of `P`. -/
noncomputable def geometricRegionCount (P : PlanarZ2Subgraph) : ℕ :=
  Nat.card {c : (regionGraph (imageGraph P)).ConnectedComponent // c.supp.Finite}

theorem mem_box_compl_of_exterior {R : ℕ} {a : Site 2} (h : a ∈ exterior 2 R) :
    a ∉ box 2 R := by
  rw [mem_exterior] at h
  rw [mem_box]; push Not
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by omega⟩

theorem rot90Inv_mem_box (R : ℕ) {x : Site 2} (hx : x ∈ box 2 R) :
    rot90Inv x ∈ box 2 R := by
  intro i; fin_cases i
  · have h : (rot90Inv x) 0 = x 1 := by simp [rot90Inv]
    change ((rot90Inv x) 0).natAbs ≤ R; rw [h]; exact hx 1
  · have h : (rot90Inv x) 1 = - x 0 := by simp [rot90Inv]
    change ((rot90Inv x) 1).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 0

theorem rot90Fun_mem_box (R : ℕ) {x : Site 2} (hx : x ∈ box 2 R) :
    rot90Fun x ∈ box 2 R := by
  intro i; fin_cases i
  · have h : (rot90Fun x) 0 = - x 1 := by simp [rot90Fun]
    change ((rot90Fun x) 0).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 1
  · have h : (rot90Fun x) 1 = x 0 := by simp [rot90Fun]
    change ((rot90Fun x) 1).natAbs ≤ R; rw [h]; exact hx 0

theorem image_subset_box (P : PlanarZ2Subgraph) :
    ∃ R : ℕ, ∀ v : P.V, P.emb v ∈ box 2 R := by
  obtain ⟨R, hR⟩ := finite_subset_box (Set.range P.emb) (Set.finite_range P.emb)
  exact ⟨R, fun v => hR ⟨v, rfl⟩⟩

theorem exterior_dual_edge_not_deleted (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2} (hf : f ∉ box 2 R) :
    crossEdge.symm s(f, g) ∉ (imageGraph P).edgeSet := by
  intro hmem
  have hsymm : crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
    simp [crossEdge, sym2Congr]
  rw [hsymm, SimpleGraph.mem_edgeSet] at hmem
  obtain ⟨x, y, _, hx, _⟩ := hmem
  have hrf : rot90Inv f ∈ box 2 R := hx ▸ hR x
  have hf_eq : f = rot90Fun (rot90Inv f) := by
    have := rot90Equiv.right_inv f
    simpa [rot90Equiv] using this.symm
  exact hf (hf_eq ▸ rot90Fun_mem_box R hrf)

theorem regionGraph_adj_of_exterior (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2}
    (hf : f ∉ box 2 R) (hadj : (hypercubicLattice 2).Adj f g) :
    (regionGraph (imageGraph P)).Adj f g :=
  ⟨hadj, exterior_dual_edge_not_deleted P R hR hf⟩

/-- Outside a box containing the image of `P`, the lattice embeds in the region graph. -/
noncomputable def exteriorToRegionHom (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) :
    ((hypercubicLattice 2).induce (exterior 2 R)) →g (regionGraph (imageGraph P)) where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    exact regionGraph_adj_of_exterior P R hR (mem_box_compl_of_exterior a.2) hab

theorem regionGraph_reachable_of_exterior (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2}
    (hf : f ∈ exterior 2 R) (hg : g ∈ exterior 2 R)
    (h : ((hypercubicLattice 2).induce (exterior 2 R)).Reachable ⟨f, hf⟩ ⟨g, hg⟩) :
    (regionGraph (imageGraph P)).Reachable f g := by
  have hmap := h.map (exteriorToRegionHom P R hR)
  simpa [exteriorToRegionHom] using hmap

theorem exists_infinite_region (P : PlanarZ2Subgraph) :
    ∃ C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  obtain ⟨R, hR⟩ := image_subset_box P
  set RG := regionGraph (imageGraph P) with hRG
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  set C0 := RG.connectedComponentMk (beacon 2 R) with hC0
  refine ⟨C0, ?_⟩
  have hExtComp : ∀ x : Site 2, x ∈ exterior 2 R → RG.connectedComponentMk x = C0 := by
    intro x hx
    exact ConnectedComponent.sound
      (regionGraph_reachable_of_exterior P R hR hx hb_ext
        (box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext))
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact hExtComp (w : Site 2) w.2

end StatMech.Lattice
