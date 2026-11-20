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

open SimpleGraph Set

namespace StatMech.Lattice














def regionGraph (G : SimpleGraph (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet
  symm := by
    intro f g ⟨hadj, hcross⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem regionGraph_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (regionGraph G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet := Iff.rfl




theorem regionGraph_le_dual (G : SimpleGraph (Site 2)) :
    regionGraph G ≤ hypercubicLattice 2 := fun _ _ h => h.1








structure PlanarZ2Subgraph where
  
  V : Type
  
  finV : Finite V
  
  decV : DecidableEq V
  
  G : SimpleGraph V
  
  emb : V ↪ Site 2
  

  isSub : ∀ ⦃x y : V⦄, G.Adj x y → (hypercubicLattice 2).Adj (emb x) (emb y)

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV





noncomputable def imageGraph (P : PlanarZ2Subgraph) : SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := by
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
    show ((rot90Inv x) 0).natAbs ≤ R; rw [h]; exact hx 1
  · have h : (rot90Inv x) 1 = - x 0 := by simp [rot90Inv]
    show ((rot90Inv x) 1).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 0



theorem rot90Fun_mem_box (R : ℕ) {x : Site 2} (hx : x ∈ box 2 R) :
    rot90Fun x ∈ box 2 R := by
  intro i; fin_cases i
  · have h : (rot90Fun x) 0 = - x 1 := by simp [rot90Fun]
    show ((rot90Fun x) 0).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 1
  · have h : (rot90Fun x) 1 = x 0 := by simp [rot90Fun]
    show ((rot90Fun x) 1).natAbs ≤ R; rw [h]; exact hx 0


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































def DiscreteJordanSeparation (P : PlanarZ2Subgraph) : Prop :=
  Nonempty ({c : (regionGraph (imageGraph P)).ConnectedComponent // c.supp.Finite}
    ≃ Fin (nullity P.G))








theorem geometricRegionCount_eq_nullity (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    geometricRegionCount P = nullity P.G := by
  obtain ⟨e⟩ := hJ
  unfold geometricRegionCount
  rw [Nat.card_eq_of_equiv_fin e]


















theorem faceCount_eq_geometric_regions (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    faceCount P.G = geometricRegionCount P + 1 := by
  rw [geometricRegionCount_eq_nullity P hJ, faceCount]










theorem euler_geometric_regions (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1)
      = 1 + Nat.card P.G.ConnectedComponent := by
  have h := euler_general P.G
  have hfc : (faceCount P.G : ℤ) = (geometricRegionCount P : ℤ) + 1 := by
    rw [faceCount_eq_geometric_regions P hJ]; push_cast; ring
  rw [hfc] at h
  linarith




theorem euler_geometric_regions_connected (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) (hC : P.G.Connected) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 2 := by
  have h := euler_geometric_regions P hJ
  rw [card_components_eq_one_of_connected hC] at h
  push_cast at h ⊢; linarith

end StatMech.Lattice
