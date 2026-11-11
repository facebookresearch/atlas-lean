/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric

/-!
# Pushing subgraphs of a planar lattice graph into `ℤ²`

Push a subgraph `K` of a `PlanarZ2Subgraph` `P` into `ℤ²`, and show that the region graph of a
finite subgraph of `ℤ²` has finitely many components.

## Main definitions

* `StatMech.Lattice.jei_pushGraph P K`: the image in `ℤ²` of a subgraph `K` of `P`.

## Main results

* `StatMech.Lattice.jei_regionComponents_finite`: the region graph of a finite subgraph of `ℤ²` has
  finitely many components.
* `StatMech.Lattice.jei_push_reachable_iff`: pushing forward preserves connectivity.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

theorem jei_sym2_mem_finite (e : Sym2 (Site 2)) : {x : Site 2 | x ∈ e}.Finite := by
  induction e with
  | _ a b =>
    apply Set.Finite.subset ((Set.finite_singleton a).insert b)
    intro x hx
    rw [Set.mem_ofPred_eq, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert _ _

theorem jei_support_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    H.support.Finite := by
  classical
  apply Set.Finite.subset
    (Set.Finite.biUnion hfin (fun e (_ : e ∈ H.edgeSet) => jei_sym2_mem_finite e))
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  rw [Set.mem_iUnion₂]
  exact ⟨s(v, w), by rwa [SimpleGraph.mem_edgeSet], Sym2.mem_mk_left v w⟩

theorem jei_exterior_dual_edge_not_deleted (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2} (hf : f ∉ box 2 R) :
    crossEdge.symm s(f, g) ∉ H.edgeSet := by
  intro hmem
  have hsymm : crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
    simp [crossEdge, sym2Congr]
  rw [hsymm, SimpleGraph.mem_edgeSet] at hmem
  have hsupp : rot90Inv f ∈ H.support := ⟨rot90Inv g, hmem⟩
  have hrf : rot90Inv f ∈ box 2 R := hR _ hsupp
  have hf_eq : f = rot90Fun (rot90Inv f) := by
    have := rot90Equiv.right_inv f
    simpa [rot90Equiv] using this.symm
  exact hf (hf_eq ▸ rot90Fun_mem_box R hrf)

theorem jei_regionGraph_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2}
    (hf : f ∉ box 2 R) (hadj : (hypercubicLattice 2).Adj f g) :
    (regionGraph H).Adj f g :=
  ⟨hadj, jei_exterior_dual_edge_not_deleted H R hR hf⟩

theorem jei_regionComponents_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    Finite (regionGraph H).ConnectedComponent := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box H.support (jei_support_finite H hfin)
  set RG := regionGraph H with hRG
  set S : Set (Site 2) := box 2 R ∪ {beacon 2 R} with hS
  have hSfin : S.Finite := (box_finite 2 R).union (Set.finite_singleton _)
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  have hExtMk : ∀ x : Site 2, x ∈ exterior 2 R →
      RG.connectedComponentMk x = RG.connectedComponentMk (beacon 2 R) := by
    intro x hx
    refine ConnectedComponent.sound ?_
    have hconn := box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext
    have hmap := hconn.map
      (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 R)) →g RG)
    · exact hmap
    · intro a b hab
      have haext : (a : Site 2) ∉ box 2 R := mem_box_compl_of_exterior a.2
      exact jei_regionGraph_adj_of_exterior H R (fun v hv => hR hv) haext hab
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 R
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hxbox
    refine ⟨beacon 2 R, Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 R) = c
    rw [← hExtMk x hxext]; exact hx

/-- The image in `ℤ²` of a subgraph `K` of a `PlanarZ2Subgraph` `P`. -/
noncomputable def jei_pushGraph (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := ⟨by rintro a b ⟨x, y, hadj, rfl, rfl⟩; exact ⟨y, x, hadj.symm, rfl, rfl⟩⟩
  loopless := ⟨by
    rintro a ⟨x, y, hadj, hx, hy⟩
    have : x = y := P.emb.injective (hx.trans hy.symm)
    exact K.irrefl (this ▸ hadj)⟩

@[simp] theorem jei_pushGraph_adj (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (a b : Site 2) :
    (jei_pushGraph P K).Adj a b ↔ ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b := Iff.rfl

theorem jei_pushGraph_G (P : PlanarZ2Subgraph) : jei_pushGraph P P.G = imageGraph P := by
  ext a b; rw [jei_pushGraph_adj, imageGraph_adj]

theorem jei_pushGraph_bot (P : PlanarZ2Subgraph) : jei_pushGraph P ⊥ = ⊥ := by
  ext a b; rw [jei_pushGraph_adj]
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨x, y, hadj, _, _⟩; exact hadj.elim

theorem jei_pushGraph_edgeSet_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    (jei_pushGraph P K).edgeSet.Finite := by
  have hV : Finite P.V := P.finV
  apply Set.Finite.subset (Set.finite_range (Sym2.map P.emb : Sym2 P.V → Sym2 (Site 2)))
  intro e he
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj] at he
    obtain ⟨x, y, hK, rfl, rfl⟩ := he
    exact ⟨s(x, y), by simp⟩

theorem jei_pushGraph_regionComponents_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Finite (regionGraph (jei_pushGraph P K)).ConnectedComponent :=
  jei_regionComponents_finite _ (jei_pushGraph_edgeSet_finite P K)

theorem jei_pushGraph_sup_edge (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V)
    (hne : x ≠ y) :
    jei_pushGraph P (K ⊔ edge x y) = jei_pushGraph P K ⊔ edge (P.emb x) (P.emb y) := by
  ext a b
  simp only [jei_pushGraph_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨u, v, huv, rfl, rfl⟩
    rcases huv with hK | ⟨hxy, _⟩
    · exact Or.inl ⟨u, v, hK, rfl, rfl⟩
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h)⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h).symm⟩
  · rintro (⟨u, v, hK, rfl, rfl⟩ | ⟨hab, hne'⟩)
    · exact ⟨u, v, Or.inl hK, rfl, rfl⟩
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, y, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩, rfl, rfl⟩
      · exact ⟨y, x, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩, rfl, rfl⟩

theorem jei_push_reachable_iff (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V) :
    (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) ↔ K.Reachable x y := by
  constructor
  · rintro ⟨w⟩
    suffices h : ∀ (a b : Site 2) (w : (jei_pushGraph P K).Walk a b) (za zb : P.V),
        P.emb za = a → P.emb zb = b → K.Reachable za zb by
      exact h _ _ w x y rfl rfl
    intro a b w
    induction w with
    | nil =>
      intro za zb hza hzb
      have : za = zb := P.emb.injective (hza.trans hzb.symm)
      subst this; exact Reachable.refl za
    | @cons c d e hcd wde ih =>
      intro za zb hza hzb
      obtain ⟨u, v, hKuv, hu, hv⟩ := hcd
      have hzau : za = u := P.emb.injective (hza.trans hu.symm)
      subst hzau
      exact (hKuv.reachable).trans (ih v zb hv hzb)
  · intro h
    refine h.map (⟨P.emb, ?_⟩ : K →g jei_pushGraph P K)
    intro a b hab; exact ⟨a, b, hab, rfl, rfl⟩

theorem jei_crossEdge_present (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) :
    crossEdge s(P.emb x, P.emb y) ∈ (regionGraph (jei_pushGraph P K)).edgeSet := by
  rw [crossEdge_mk, SimpleGraph.mem_edgeSet, regionGraph_adj]
  refine ⟨(rot90_adj _ _).mpr (P.isSub hadjG), ?_⟩
  rw [← crossEdge_mk, Equiv.symm_apply_apply, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst_vars
  exact hnotK hKuv

end Lattice

end StatMech
