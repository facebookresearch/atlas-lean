/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.PlanarTopology

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice








namespace EvenDegree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



theorem sum_degree_component_even (C : G.ConnectedComponent) :
    Even (∑ x ∈ C.supp.toFinset, G.degree x) := by
  classical
  have hdeg : ∀ x : (C.supp : Set V), (G.induce (C.supp : Set V)).degree x = G.degree x := by
    intro x
    apply degree_induce_of_neighborSet_subset
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    show G.connectedComponentMk y = C
    have hx : G.connectedComponentMk (x : V) = C := x.2
    rw [← hx]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hy.symm
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce (C.supp : Set V))
  have key : ∑ x : (C.supp : Set V), G.degree (x : V)
      = 2 * #(G.induce (C.supp : Set V)).edgeFinset := by
    rw [← hhand]
    exact (Finset.sum_congr rfl (fun x _ => (hdeg x).symm))
  have hconv : ∑ x ∈ C.supp.toFinset, G.degree x = ∑ x : (C.supp : Set V), G.degree (x : V) := by
    rw [← Finset.sum_coe_sort C.supp.toFinset (fun x => G.degree x)]
    apply Finset.sum_bij (fun (x : C.supp.toFinset) _ => (⟨x.1, by
      have := x.2; rwa [Set.mem_toFinset] at this⟩ : (C.supp : Set V)))
    · intro a _; exact Finset.mem_univ _
    · intro a _ b _ h; ext; simpa using congrArg Subtype.val h
    · intro b _; exact ⟨⟨b.1, by rw [Set.mem_toFinset]; exact b.2⟩, Finset.mem_univ _, rfl⟩
    · intro a _; rfl
  rw [hconv, key]
  exact even_two_mul _



theorem degree_deleteEdges_of_ne {v w x : V} (hxv : x ≠ v) (hxw : x ≠ w) :
    (G.deleteEdges {s(v, w)}).degree x = G.degree x := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1
  apply Finset.ext
  intro y
  simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro hcontra
    rw [Sym2.eq_iff] at hcontra
    rcases hcontra with ⟨hxv', _⟩ | ⟨hxw', _⟩
    · exact hxv hxv'
    · exact hxw hxw'



theorem degree_deleteEdges_self {v w : V} (hadj : G.Adj v w) :
    (G.deleteEdges {s(v, w)}).degree v + 1 = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hsub : (G.deleteEdges {s(v, w)}).neighborFinset v =
      (G.neighborFinset v).erase w := by
    apply Finset.ext
    intro y
    simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hxy, hne⟩
      refine ⟨?_, hxy⟩
      intro hyw; subst hyw; exact hne rfl
    · rintro ⟨hyw, hxy⟩
      refine ⟨hxy, ?_⟩
      intro hcontra
      rw [Sym2.eq_iff] at hcontra
      rcases hcontra with ⟨_, hyw'⟩ | ⟨hvw, _⟩
      · exact hyw hyw'
      · exact (hadj.ne) hvw
  rw [hsub, Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hadj)]
  have hpos : 0 < #(G.neighborFinset v) := by
    rw [card_neighborFinset_eq_degree]
    exact hadj.degree_pos_left
  omega



theorem reachable_deleteEdges_of_even (heven : ∀ x, Even (G.degree x))
    {v w : V} (hadj : G.Adj v w) :
    (G.deleteEdges {s(v, w)}).Reachable v w := by
  classical
  by_contra hnr
  set H := G.deleteEdges {s(v, w)} with hH
  set C := H.connectedComponentMk v with hC
  have hwC : w ∉ (C.supp : Set V) := by
    intro hw
    apply hnr
    have hwmk : H.connectedComponentMk w = C := hw
    rw [hC] at hwmk
    exact (ConnectedComponent.eq.mp hwmk).symm
  have hHeven := sum_degree_component_even H C
  have hvC : v ∈ C.supp.toFinset := by
    rw [Set.mem_toFinset]; show H.connectedComponentMk v = C; rw [hC]
  have hxne_w : ∀ x ∈ C.supp.toFinset, x ≠ w := by
    intro x hx hxw
    rw [Set.mem_toFinset] at hx
    exact hwC (hxw ▸ hx)
  have hsplit : (∑ x ∈ C.supp.toFinset, H.degree x) + 1 =
      ∑ x ∈ C.supp.toFinset, G.degree x := by
    rw [← Finset.add_sum_erase _ _ hvC, ← Finset.add_sum_erase _ (fun x => G.degree x) hvC]
    have hrest : ∑ x ∈ C.supp.toFinset.erase v, H.degree x
        = ∑ x ∈ C.supp.toFinset.erase v, G.degree x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      have hxw : x ≠ w := hxne_w x (Finset.mem_of_mem_erase hx)
      exact degree_deleteEdges_of_ne G hxv hxw
    have hvdeg : H.degree v + 1 = G.degree v := degree_deleteEdges_self G hadj
    rw [hrest]
    omega
  have hGeven : Even (∑ x ∈ C.supp.toFinset, G.degree x) :=
    Finset.even_sum _ (fun x _ => heven x)
  rw [← hsplit] at hGeven
  exact (Nat.even_add_one.mp hGeven) hHeven




theorem exists_cycle_through_edge_of_even (heven : ∀ x, Even (G.degree x))
    {v w : V} (hadj : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges :=
  adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hadj, reachable_deleteEdges_of_even G heven hadj⟩

end EvenDegree

namespace EvenDegree

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]





theorem exists_cycle_through_edge_of_even_of_finite_support
    (T : Finset V) (hsupp : G.support ⊆ (T : Set V))
    (heven : ∀ x, Even (G.degree x)) {v w : V} (hadj : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  set H := G.induce (T : Set V) with hH
  haveI : Fintype (T : Set V) := FinsetCoe.fintype T
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hvT : v ∈ (T : Set V) := hsupp hadj.mem_support_left
  have hwT : w ∈ (T : Set V) := hsupp hadj.mem_support_right
  have hdegH : ∀ x : (T : Set V), H.degree x = G.degree (x : V) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    refine Fintype.card_congr ?_
    refine ⟨fun y => ⟨(y.1 : V), y.2⟩, fun y => ⟨⟨y.1, hsupp y.2.symm.mem_support_left⟩, y.2⟩,
      ?_, ?_⟩
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hHeven : ∀ x : (T : Set V), Even (H.degree x) := by
    intro x; rw [hdegH x]; exact heven _
  have hadjH : H.Adj ⟨v, hvT⟩ ⟨w, hwT⟩ := hadj
  obtain ⟨u, p, hpcyc, hpe⟩ := exists_cycle_through_edge_of_even H hHeven hadjH
  let emb : H ↪g G := SimpleGraph.Embedding.induce (T : Set V)
  refine ⟨(u : V), p.map emb.toHom, hpcyc.map emb.injective, ?_⟩
  have hmem : s((⟨v, hvT⟩ : (T : Set V)), (⟨w, hwT⟩ : (T : Set V))) ∈ p.edges := hpe
  have hmap := SimpleGraph.Walk.edges_map (f := emb.toHom) (p := p)
  have hgoal : s(v, w)
      = Sym2.map emb.toHom s((⟨v, hvT⟩ : (T : Set V)), (⟨w, hwT⟩ : (T : Set V))) := by
    simp only [Sym2.map_mk]; rfl
  have hin : s(v, w) ∈ List.map (Sym2.map emb.toHom) p.edges := by
    rw [List.mem_map]; exact ⟨_, hmem, hgoal.symm⟩
  rwa [← hmap] at hin

end EvenDegree










noncomputable def sharedPrimalEdge (f g : Site 2) : Sym2 (Site 2) := by
  classical
  exact if f 0 = g 0 then
    s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)])
  else
    s(![max (f 0) (g 0), f 1], ![max (f 0) (g 0), f 1 + 1])


theorem sharedPrimalEdge_right (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a + 1, b] = s(faceCorner10 a b, faceCorner11 a b) := by
  unfold sharedPrimalEdge faceCorner10 faceCorner11
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max a (a + 1) = a + 1 by omega]


theorem sharedPrimalEdge_left (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(faceCorner00 a b, faceCorner01 a b) := by
  unfold sharedPrimalEdge faceCorner00 faceCorner01
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max a (a - 1) = a by omega]


theorem sharedPrimalEdge_top (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b + 1] = s(faceCorner01 a b, faceCorner11 a b) := by
  unfold sharedPrimalEdge faceCorner01 faceCorner11
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b + 1) = b + 1 by omega]


theorem sharedPrimalEdge_bottom (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b - 1] = s(faceCorner00 a b, faceCorner10 a b) := by
  unfold sharedPrimalEdge faceCorner00 faceCorner10
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b - 1) = b by omega]



def bdEdge (S : Set (Site 2)) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y => (x ∈ S ↔ y ∉ S), by
    intro x y
    simp only [eq_iff_iff]
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp_all⟩ e

@[simp] theorem bdEdge_mk (S : Set (Site 2)) (x y : Site 2) :
    bdEdge S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := by
  unfold bdEdge; rfl

theorem bdEdge_iff_bdInd (S : Set (Site 2)) (x y : Site 2) :
    bdEdge S s(x, y) ↔ bdInd S x y = 1 := by
  rw [bdEdge_mk]
  unfold bdInd
  by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]


theorem sharedPrimalEdge_comm_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge f g = sharedPrimalEdge g f := by
  classical
  unfold sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0.symm, h0, max_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm)]
    have hadj := h
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : f 1 = g 1 := by
      by_contra hne
      have : (f 1 - g 1).natAbs ≥ 1 := by omega
      have : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    rw [h1, max_comm]





def faceBoundaryGraph (S : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ bdEdge S (sharedPrimalEdge f g)
  symm := by
    intro f g ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [← sharedPrimalEdge_comm_of_adj hadj]
  loopless := by
    refine ⟨fun f h => ?_⟩
    exact (hypercubicLattice 2).irrefl h.1

@[simp] theorem faceBoundaryGraph_adj (S : Set (Site 2)) (f g : Site 2) :
    (faceBoundaryGraph S).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ bdEdge S (sharedPrimalEdge f g) := Iff.rfl


theorem faceBoundaryGraph_le (S : Set (Site 2)) :
    faceBoundaryGraph S ≤ hypercubicLattice 2 := fun _ _ h => h.1



noncomputable instance instLocallyFiniteFaceBoundaryGraph (S : Set (Site 2)) :
    SimpleGraph.LocallyFinite (faceBoundaryGraph S) := by
  classical
  exact fun f =>
    Fintype.ofFinset
      ((candFinset 2 f).filter (fun g => (faceBoundaryGraph S).Adj f g)) (by
        intro g
        rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        exact mem_candFinset_of_adj 2 f g (faceBoundaryGraph_le S h))



theorem latAdj_right (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_left (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_top (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_bottom (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b - 1] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]



theorem candFinset_face (a b : ℤ) :
    candFinset 2 ![a, b] =
      ({![a + 1, b], ![a - 1, b], ![a, b + 1], ![a, b - 1]} : Finset (Site 2)) := by
  have huniv : (Finset.univ : Finset (Fin 2 × Bool))
      = {(0, true), (0, false), (1, true), (1, false)} := by decide
  unfold candFinset
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton]
  have e0 : candMap 2 ![a, b] (0, true) = ![a + 1, b] := by
    unfold candMap shift; funext i; fin_cases i <;> simp
  have e1 : candMap 2 ![a, b] (0, false) = ![a - 1, b] := by
    unfold candMap shift; funext i; fin_cases i <;> (simp; try ring)
  have e2 : candMap 2 ![a, b] (1, true) = ![a, b + 1] := by
    unfold candMap shift; funext i; fin_cases i <;> simp
  have e3 : candMap 2 ![a, b] (1, false) = ![a, b - 1] := by
    unfold candMap shift; funext i; fin_cases i <;> (simp; try ring)
  rw [e0, e1, e2, e3]

open Classical in


theorem neighborFinset_faceBoundaryGraph (S : Set (Site 2)) (f : Site 2) :
    (faceBoundaryGraph S).neighborFinset f =
      (candFinset 2 f).filter (fun g => (faceBoundaryGraph S).Adj f g) := by
  apply Finset.ext
  intro g
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  refine ⟨fun h => ⟨mem_candFinset_of_adj 2 f g (faceBoundaryGraph_le S h), h⟩, fun h => h.2⟩




theorem degree_faceBoundaryGraph (S : Set (Site 2)) (a b : ℤ) :
    (faceBoundaryGraph S).degree ![a, b] = faceBoundaryDegree S a b := by
  classical
  rw [SimpleGraph.degree, neighborFinset_faceBoundaryGraph, candFinset_face]
  have hr : (faceBoundaryGraph S).Adj ![a, b] ![a + 1, b]
      ↔ bdInd S (faceCorner10 a b) (faceCorner11 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_right, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_right a b)
  have hl : (faceBoundaryGraph S).Adj ![a, b] ![a - 1, b]
      ↔ bdInd S (faceCorner00 a b) (faceCorner01 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_left, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_left a b)
  have ht : (faceBoundaryGraph S).Adj ![a, b] ![a, b + 1]
      ↔ bdInd S (faceCorner01 a b) (faceCorner11 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_top, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_top a b)
  have hb : (faceBoundaryGraph S).Adj ![a, b] ![a, b - 1]
      ↔ bdInd S (faceCorner00 a b) (faceCorner10 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_bottom, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_bottom a b)
  
  have d0 : ∀ x y : ℤ, x ≠ y → (![x, b] : Site 2) ≠ ![y, b] := by
    intro x y hxy h; apply hxy; have := congrFun h 0
    simpa only [Matrix.cons_val_zero] using this
  have d1 : ∀ x y : ℤ, x ≠ y → (![a, x] : Site 2) ≠ ![a, y] := by
    intro x y hxy h; apply hxy; have := congrFun h 1
    simpa only [Matrix.cons_val_one, Matrix.head_cons] using this
  have d12 : (![a + 1, b] : Site 2) ≠ ![a - 1, b] := d0 _ _ (by omega)
  have d13 : (![a + 1, b] : Site 2) ≠ ![a, b + 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d14 : (![a + 1, b] : Site 2) ≠ ![a, b - 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d23 : (![a - 1, b] : Site 2) ≠ ![a, b + 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d24 : (![a - 1, b] : Site 2) ≠ ![a, b - 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d34 : (![a, b + 1] : Site 2) ≠ ![a, b - 1] := d1 _ _ (by omega)
  unfold faceBoundaryDegree
  rw [Finset.card_filter]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact d34),
      Finset.sum_singleton]
  have cast_ite : ∀ (P : Prop) [Decidable P] (n : ℕ), (P ↔ n = 1) → n ≤ 1 →
      (if P then 1 else 0) = n := by
    intro P _ n hPn _
    by_cases hP : P
    · rw [if_pos hP]; exact (hPn.mp hP).symm
    · rw [if_neg hP]
      have : n ≠ 1 := fun h => hP (hPn.mpr h)
      omega
  have hle : ∀ x y : Site 2, bdInd S x y ≤ 1 := by
    intro x y; unfold bdInd; by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]
  rw [cast_ite _ _ hr (hle _ _), cast_ite _ _ hl (hle _ _),
      cast_ite _ _ ht (hle _ _), cast_ite _ _ hb (hle _ _)]
  rw [bdInd_comm S (faceCorner00 a b) (faceCorner01 a b),
      bdInd_comm S (faceCorner01 a b) (faceCorner11 a b)]
  ring




theorem degree_faceBoundaryGraph_even (S : Set (Site 2)) (f : Site 2) :
    Even ((faceBoundaryGraph S).degree f) := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rw [hf, degree_faceBoundaryGraph]
  rw [Nat.even_iff]
  exact faceBoundaryDegree_even S (f 0) (f 1)





def cornerFaces (c : Site 2) : Finset (Site 2) :=
  {![c 0 - 1, c 1 - 1], ![c 0 - 1, c 1], ![c 0, c 1 - 1], ![c 0, c 1]}


theorem site2_eq (x y x' y' : ℤ) : (![x, y] : Site 2) = ![x', y'] ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl



theorem mem_cornerFaces_of_corner (a b : ℤ) (c : Site 2)
    (hc : c = ![a, b] ∨ c = ![a + 1, b] ∨ c = ![a + 1, b + 1] ∨ c = ![a, b + 1]) :
    (![a, b] : Site 2) ∈ cornerFaces c := by
  have mk : ∀ x y : ℤ, x = a → y = b → (![x, y] : Site 2) = ![a, b] := by
    rintro x y rfl rfl; rfl
  rcases hc with rfl | rfl | rfl | rfl
  · show (![a, b] : Site 2) ∈ cornerFaces ![a, b]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]
  · show (![a, b] : Site 2) ∈ cornerFaces ![a + 1, b]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; rw [Finset.mem_insert]
    exact Or.inl (mk (a + 1 - 1) b (by omega) rfl).symm
  · show (![a, b] : Site 2) ∈ cornerFaces ![a + 1, b + 1]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.mem_insert]
    exact Or.inl (mk (a + 1 - 1) (b + 1 - 1) (by omega) (by omega)).symm
  · show (![a, b] : Site 2) ∈ cornerFaces ![a, b + 1]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    rw [Finset.mem_insert]
    exact Or.inl (mk a (b + 1 - 1) rfl (by omega)).symm




theorem support_faceBoundaryGraph_subset (S : Set (Site 2)) :
    (faceBoundaryGraph S).support ⊆ ⋃ c ∈ S, (cornerFaces c : Set (Site 2)) := by
  intro f hf
  rw [SimpleGraph.mem_support] at hf
  obtain ⟨g, hadj⟩ := hf
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hdeg : 0 < faceBoundaryDegree S (f 0) (f 1) := by
    rw [← degree_faceBoundaryGraph]
    rw [← hfeq]
    exact hadj.degree_pos_left
  have hcorner : (![f 0, f 1] : Site 2) ∈ S ∨ (![f 0 + 1, f 1] : Site 2) ∈ S
      ∨ (![f 0 + 1, f 1 + 1] : Site 2) ∈ S ∨ (![f 0, f 1 + 1] : Site 2) ∈ S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2, h3⟩ := hcon
    have e1 : bdInd S (faceCorner00 (f 0) (f 1)) (faceCorner10 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner00 faceCorner10; rw [if_neg]; tauto
    have e2 : bdInd S (faceCorner10 (f 0) (f 1)) (faceCorner11 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner10 faceCorner11; rw [if_neg]; tauto
    have e3 : bdInd S (faceCorner11 (f 0) (f 1)) (faceCorner01 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner11 faceCorner01; rw [if_neg]; tauto
    have e4 : bdInd S (faceCorner01 (f 0) (f 1)) (faceCorner00 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner01 faceCorner00; rw [if_neg]; tauto
    unfold faceBoundaryDegree at hdeg
    rw [e1, e2, e3, e4] at hdeg
    omega
  rw [Set.mem_iUnion]
  rcases hcorner with h | h | h | h
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inl rfl)⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inl rfl))⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inr (Or.inr rfl)))⟩⟩



theorem exists_finset_support_faceBoundaryGraph (S : Set (Site 2)) (hS : S.Finite) :
    ∃ T : Finset (Site 2), (faceBoundaryGraph S).support ⊆ (T : Set (Site 2)) := by
  classical
  refine ⟨hS.toFinset.biUnion cornerFaces, ?_⟩
  intro f hf
  have hf' := support_faceBoundaryGraph_subset S hf
  rw [Set.mem_iUnion] at hf'
  obtain ⟨c, hc⟩ := hf'
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcS, hfc⟩ := hc
  rw [Finset.coe_biUnion]
  rw [Set.mem_iUnion]
  exact ⟨c, Set.mem_iUnion.mpr ⟨hS.mem_toFinset.mpr hcS, hfc⟩⟩






theorem exists_faceBoundaryGraph_adj_of_edgeBoundary (S : Set (Site 2)) {x y : Site 2}
    (h : (x, y) ∈ edgeBoundary 2 S) :
    ∃ f g : Site 2, (faceBoundaryGraph S).Adj f g := by
  obtain ⟨hadj, hsplit⟩ := h
  have hsplit_swap : (y ∈ S ↔ x ∉ S) := by
    classical
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> tauto
  have hnn : NearestNeighbour 2 x y := hadj
  rw [nearestNeighbour_iff_shift] at hnn
  obtain ⟨j, s, hs, hys⟩ := hnn
  set p := x 0 with hp
  set q := x 1 with hq
  have hx : x = ![p, q] := by funext i; fin_cases i <;> rfl
  fin_cases j
  · rcases hs with rfl | rfl
    · 
      have hy : y = ![p + 1, q] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> simp
      refine ⟨![p, q], ![p, q - 1], latAdj_bottom p q, ?_⟩
      rw [sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rw [bdEdge_mk, ← hx, ← hy]
      exact hsplit
    · 
      have hy : y = ![p - 1, q] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> (simp; try ring)
      refine ⟨![p - 1, q], ![p - 1, q - 1], latAdj_bottom (p - 1) q, ?_⟩
      rw [sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rw [bdEdge_mk]
      rw [show (p - 1) + 1 = p by ring]
      rw [← hx, ← hy]; exact hsplit_swap
  · rcases hs with rfl | rfl
    · 
      have hy : y = ![p, q + 1] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> simp
      refine ⟨![p, q], ![p - 1, q], latAdj_left p q, ?_⟩
      rw [sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rw [bdEdge_mk, ← hx, ← hy]
      exact hsplit
    · 
      have hy : y = ![p, q - 1] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> (simp; try ring)
      refine ⟨![p, q - 1], ![p - 1, q - 1], latAdj_left p (q - 1), ?_⟩
      rw [sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rw [bdEdge_mk]
      rw [show (q - 1) + 1 = q by ring]
      rw [← hx, ← hy]; exact hsplit_swap









theorem exists_dualCircuit_of_finite_of_edgeBoundary (S : Set (Site 2)) (hS : S.Finite)
    {x y : Site 2} (hxy : (x, y) ∈ edgeBoundary 2 S) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph S).Walk u u), c.IsCycle := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph S hS
  obtain ⟨f, g, hfg⟩ := exists_faceBoundaryGraph_adj_of_edgeBoundary S hxy
  obtain ⟨u, c, hcyc, _⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph S) T hT (degree_faceBoundaryGraph_even S) hfg
  exact ⟨u, c, hcyc⟩














theorem exists_dualCircuit_of_finite_cluster {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) {z : Site 2}
    (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle := by
  
  obtain ⟨a, b, hab⟩ :=
    walk_mem_edgeBoundary (cluster 2 ω o) w (self_mem_cluster ω o) hz
  exact exists_dualCircuit_of_finite_of_edgeBoundary (cluster 2 ω o) hfin hab

end Lattice

end StatMech
