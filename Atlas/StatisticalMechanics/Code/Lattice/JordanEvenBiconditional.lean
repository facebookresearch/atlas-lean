/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.WindingColoring
import Code.Lattice.JordanEvenClose

open SimpleGraph Set

namespace StatMech

namespace Lattice














@[reducible]
noncomputable def jeb_induceLF {V : Type*} (H : SimpleGraph V) [SimpleGraph.LocallyFinite H]
    (s : Set V) : SimpleGraph.LocallyFinite (H.induce s) := by
  classical
  intro v
  rw [SimpleGraph.neighborSet_induce]
  apply Set.Finite.fintype
  apply Set.Finite.preimage (Function.Injective.injOn Subtype.coe_injective)
  exact (H.neighborSet ↑v).toFinite




theorem jeb_degree_induce_eq_of_neighborSet_subset {V : Type*} (H : SimpleGraph V)
    [SimpleGraph.LocallyFinite H] (s : Set V) (v : s) (hsub : H.neighborSet ↑v ⊆ s) :
    @SimpleGraph.degree _ (H.induce s) v (jeb_induceLF H s v) = H.degree ↑v := by
  classical
  have e : ((H.induce s).neighborSet v) ≃ (H.neighborSet ↑v) :=
    (Equiv.setCongr (H.neighborSet_induce s v)).trans
      { toFun := fun w => ⟨↑(w : s), w.2⟩
        invFun := fun w => ⟨⟨↑(w : V), hsub w.2⟩, w.2⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun w => by ext; rfl }
  rw [← @SimpleGraph.card_neighborSet_eq_degree _ (H.induce s) v (jeb_induceLF H s v)]
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact @Fintype.card_congr _ _ (jeb_induceLF H s v) _ e




theorem jeb_degree_induce_eq {V : Type*} (H : SimpleGraph V) [SimpleGraph.LocallyFinite H]
    (s : Set V) (hsupp : H.support ⊆ s) (v : s) :
    @SimpleGraph.degree _ (H.induce s) v (jeb_induceLF H s v) = H.degree ↑v :=
  jeb_degree_induce_eq_of_neighborSet_subset H s v
    ((H.neighborSet_subset_support ↑v).trans hsupp)






theorem jeb_degree_induce_eq' {V : Type*} (H : SimpleGraph V) [SimpleGraph.LocallyFinite H]
    (s : Set V) (v : s) (hsub : H.neighborSet ↑v ⊆ s)
    [inst : Fintype ((H.induce s).neighborSet v)] :
    (H.induce s).degree v = H.degree ↑v := by
  classical
  have e : ((H.induce s).neighborSet v) ≃ (H.neighborSet ↑v) :=
    (Equiv.setCongr (H.neighborSet_induce s v)).trans
      { toFun := fun w => ⟨↑(w : s), w.2⟩
        invFun := fun w => ⟨⟨↑(w : V), hsub w.2⟩, w.2⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun w => by ext; rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr e















theorem jeb_neighborSet_subset_component {V : Type*} (G : SimpleGraph V)
    (C : G.ConnectedComponent) (v : (C.supp : Set V)) :
    G.neighborSet ↑v ⊆ (C.supp : Set V) := by
  intro w hw
  rw [SimpleGraph.mem_neighborSet] at hw
  have hv : (↑v : V) ∈ C.supp := v.2
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ⊢
  rw [← hv]
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hw).symm







theorem jeb_two_odd_reachable_fin {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : V) (hp : Odd (G.degree p)) (hq : Odd (G.degree q))
    (hother : ∀ v, v ≠ p → v ≠ q → Even (G.degree v)) : G.Reachable p q := by
  classical
  by_contra hnr
  set C := G.connectedComponentMk p with hC
  set s : Set V := (C.supp : Set V) with hs
  have hph := SimpleGraph.even_card_odd_degree_vertices (G.induce s)
  have hdeg : ∀ v : s, (G.induce s).degree v = G.degree ↑v := fun v =>
    jeb_degree_induce_eq' G s v (jeb_neighborSet_subset_component G C v)
  have hset : (Finset.univ.filter (fun v : s => Odd ((G.induce s).degree v)))
      = Finset.univ.filter (fun v : s => Odd (G.degree ↑v)) := by
    apply Finset.filter_congr; intro v _; rw [hdeg]
  rw [hset] at hph
  have hps : p ∈ s := by rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
  have hqs : q ∉ s := by
    intro hq'
    rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC,
      SimpleGraph.ConnectedComponent.eq] at hq'
    exact hnr hq'.symm
  have hsingle : (Finset.univ.filter (fun v : s => Odd (G.degree ↑v))) = {(⟨p, hps⟩ : s)} := by
    ext v
    rw [Finset.mem_filter_univ, Finset.mem_singleton]
    constructor
    · intro hodd
      by_contra hne
      have hvp : (↑v : V) ≠ p := fun h => hne (Subtype.ext h)
      have hvq : (↑v : V) ≠ q := fun h => hqs (h ▸ v.2)
      exact (Nat.not_odd_iff_even.mpr (hother ↑v hvp hvq)) hodd
    · rintro rfl; exact hp
  rw [hsingle] at hph
  simp only [Finset.card_singleton] at hph
  exact (Nat.not_even_iff_odd.mpr ⟨0, rfl⟩) hph











theorem jeb_support_finite_of_edgeSet {V : Type*} (H : SimpleGraph V) [Fintype H.edgeSet] :
    H.support.Finite := by
  classical
  have hsub : H.support ⊆ ⋃ e ∈ H.edgeSet, {v | v ∈ e} := by
    intro v hv
    rw [SimpleGraph.mem_support] at hv
    obtain ⟨w, hw⟩ := hv
    rw [Set.mem_iUnion₂]
    exact ⟨s(v, w), (SimpleGraph.mem_edgeSet H).mpr hw, by simp⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion H.edgeSet.toFinite (fun e _ => ?_)
  exact (e.toFinset : Set V).toFinite.subset (by intro x hx; simp_all [Sym2.mem_toFinset])







theorem jeb_two_odd_reachable {V : Type*} (H : SimpleGraph V) [SimpleGraph.LocallyFinite H]
    (hfin : H.support.Finite) (p q : V)
    (hp : Odd (H.degree p)) (hq : Odd (H.degree q))
    (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) : H.Reachable p q := by
  classical
  set s : Set V := H.support ∪ {p, q} with hs
  have hsfin : s.Finite := hfin.union (Set.toFinite _)
  haveI : Fintype ↥s := hsfin.fintype
  have hsupp : H.support ⊆ s := Set.subset_union_left
  have hps : p ∈ s := Or.inr (by left; rfl)
  have hqs : q ∈ s := Or.inr (by right; rfl)
  haveI : DecidableRel (H.induce s).Adj := Classical.decRel _
  have hdegeq : ∀ v : s, H.neighborSet ↑v ⊆ s → (H.induce s).degree v = H.degree ↑v :=
    fun v hsub => jeb_degree_induce_eq' H s v hsub
  have hreach : (H.induce s).Reachable ⟨p, hps⟩ ⟨q, hqs⟩ := by
    apply jeb_two_odd_reachable_fin (H.induce s) ⟨p, hps⟩ ⟨q, hqs⟩
    · rw [hdegeq ⟨p, hps⟩ ((H.neighborSet_subset_support p).trans hsupp)]; exact hp
    · rw [hdegeq ⟨q, hqs⟩ ((H.neighborSet_subset_support q).trans hsupp)]; exact hq
    · intro v hvp hvq
      rw [hdegeq v ((H.neighborSet_subset_support ↑v).trans hsupp)]
      exact hother ↑v (fun h => hvp (Subtype.ext h)) (fun h => hvq (Subtype.ext h))
  have := hreach.map (SimpleGraph.Embedding.induce s).toHom
  simpa using this





theorem jeb_two_odd_reachable_of_edgeSet {V : Type*} (H : SimpleGraph V)
    [SimpleGraph.LocallyFinite H] [Fintype H.edgeSet] (p q : V)
    (hp : Odd (H.degree p)) (hq : Odd (H.degree q))
    (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) : H.Reachable p q :=
  jeb_two_odd_reachable H (jeb_support_finite_of_edgeSet H) p q hp hq hother











theorem jeb_site_eq_iff (x : Site 2) (c d : ℤ) : x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp_all


theorem jeb_jce_nbr_inj (v : Site 2) : Function.Injective (jce_nbr v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso; simp only [jce_nbr] at h; rw [funext_iff] at h
       have h0 := h 0; have h1 := h 1
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1; omega)


theorem jeb_exists_jce_nbr (v w : Site 2) (h : (hypercubicLattice 2).Adj v w) :
    ∃ i : Fin 4, w = jce_nbr v i := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  have hcase : (v 0 = w 0 ∧ (w 1 = v 1 + 1 ∨ w 1 = v 1 - 1)) ∨
         (v 1 = w 1 ∧ (w 0 = v 0 + 1 ∨ w 0 = v 0 - 1)) := by omega
  rcases hcase with ⟨h0, (h1|h1)⟩ | ⟨h1, (h0|h0)⟩
  · refine ⟨2, ?_⟩; rw [jce_nbr, jeb_site_eq_iff]; omega
  · refine ⟨3, ?_⟩; rw [jce_nbr, jeb_site_eq_iff]; omega
  · refine ⟨0, ?_⟩; rw [jce_nbr, jeb_site_eq_iff]; omega
  · refine ⟨1, ?_⟩; rw [jce_nbr, jeb_site_eq_iff]; omega





theorem jeb_jce_degree_eq_degree (H : SimpleGraph (Site 2)) [SimpleGraph.LocallyFinite H]
    (hsub : H ≤ hypercubicLattice 2) (v : Site 2) :
    jce_degree H.edgeSet v = H.degree v := by
  classical
  rw [jce_degree, ← SimpleGraph.card_neighborSet_eq_degree, ← Set.toFinset_card]
  apply Finset.card_bij (fun i _ => jce_nbr v i)
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet]
    rw [SimpleGraph.mem_edgeSet] at hi
    exact hi.2
  · intro i _ j _ h; exact jeb_jce_nbr_inj v h
  · intro w hw
    rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet] at hw
    obtain ⟨i, hi⟩ := jeb_exists_jce_nbr v w (hsub hw)
    refine ⟨i, ?_, hi.symm⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [SimpleGraph.mem_edgeSet, ← hi]; exact hw⟩












theorem jeb_jce_degree_insert_endpoint (E : Set (Sym2 (Site 2)))
    (p q : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ E) :
    jce_degree (insert (s(p,q)) E) p = jce_degree E p + 1 := by
  classical
  obtain ⟨i0, hi0⟩ := jeb_exists_jce_nbr p q hpq
  have hpq_ne : p ≠ q := hpq.ne
  have hnotE : s(p, jce_nbr p i0) ∉ E := by rw [← hi0]; exact hnpq
  have memInsert : ∀ i : Fin 4, (s(p, jce_nbr p i) ∈ insert (s(p,q)) E)
      ↔ (i = i0 ∨ s(p, jce_nbr p i) ∈ E) := by
    intro i
    rw [Set.mem_insert_iff]
    refine ⟨?_, ?_⟩
    · rintro (heq | hmem)
      · left; apply jeb_jce_nbr_inj p; rw [← hi0]
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exact absurd h1 hpq_ne
      · right; exact hmem
    · rintro (rfl | hmem)
      · left; rw [← hi0]
      · right; exact hmem
  have key : ∀ i : Fin 4, (if s(p, jce_nbr p i) ∈ insert (s(p,q)) E then (1:ℕ) else 0)
      = (if s(p, jce_nbr p i) ∈ E then 1 else 0) + (if i = i0 then 1 else 0) := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [if_pos ((memInsert i).mpr (Or.inl rfl)), if_neg hnotE, if_pos rfl]
    · rw [if_neg hi, add_zero]
      by_cases hmem : s(p, jce_nbr p i) ∈ E
      · rw [if_pos ((memInsert i).mpr (Or.inr hmem)), if_pos hmem]
      · rw [if_neg hmem, if_neg (fun h => ((memInsert i).mp h).elim hi hmem)]
  have step1 : (∑ i : Fin 4, if s(p, jce_nbr p i) ∈ insert (s(p,q)) E then (1:ℕ) else 0)
      = ∑ i : Fin 4, ((if s(p, jce_nbr p i) ∈ E then (1:ℕ) else 0)
          + (if i = i0 then (1:ℕ) else 0)) := Finset.sum_congr rfl (fun i _ => key i)
  have step2 : (∑ i : Fin 4, ((if s(p, jce_nbr p i) ∈ E then (1:ℕ) else 0)
          + (if i = i0 then (1:ℕ) else 0)))
      = (∑ i : Fin 4, if s(p, jce_nbr p i) ∈ E then (1:ℕ) else 0) + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i0 (fun _ => (1:ℕ)),
      if_pos (Finset.mem_univ _)]
  simp only [jce_degree, Finset.card_filter]
  convert step1.trans step2 using 3



theorem jeb_jce_degree_insert_other (E : Set (Sym2 (Site 2)))
    (p q v : Site 2) (hvp : v ≠ p) (hvq : v ≠ q) :
    jce_degree (insert (s(p,q)) E) v = jce_degree E v := by
  classical
  have key : ∀ i : Fin 4, (if s(v, jce_nbr v i) ∈ insert (s(p,q)) E then (1:ℕ) else 0)
      = (if s(v, jce_nbr v i) ∈ E then 1 else 0) := by
    intro i
    have hne : s(v, jce_nbr v i) ≠ s(p, q) := by
      rw [ne_eq, Sym2.eq_iff]; push Not
      exact ⟨fun h1 _ => hvp h1, fun h1 _ => hvq h1⟩
    by_cases hmem : s(v, jce_nbr v i) ∈ E
    · rw [if_pos (Set.mem_insert_of_mem _ hmem), if_pos hmem]
    · rw [if_neg hmem, if_neg (by rw [Set.mem_insert_iff]; push Not; exact ⟨hne, hmem⟩)]
  have step : (∑ i : Fin 4, if s(v, jce_nbr v i) ∈ insert (s(p,q)) E then (1:ℕ) else 0)
      = ∑ i : Fin 4, if s(v, jce_nbr v i) ∈ E then (1:ℕ) else 0 :=
    Finset.sum_congr rfl (fun i _ => key i)
  simp only [jce_degree, Finset.card_filter]
  convert step using 3














theorem jeb_degree_data_of_closedContour (H : SimpleGraph (Site 2))
    [SimpleGraph.LocallyFinite H] (hsub : H ≤ hypercubicLattice 2) (p q : Site 2)
    (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hcc : jce_ClosedContour (insert (s(p,q)) H.edgeSet)) :
    Odd (H.degree p) ∧ Odd (H.degree q) ∧ (∀ v, v ≠ p → v ≠ q → Even (H.degree v)) := by
  have hqp : s(q, p) ∉ H.edgeSet := fun h => hnpq (by rwa [Sym2.eq_swap] at h)
  refine ⟨?_, ?_, ?_⟩
  · have := hcc p
    rw [jeb_jce_degree_insert_endpoint H.edgeSet p q hpq hnpq,
      jeb_jce_degree_eq_degree H hsub p] at this
    rwa [Nat.even_add_one, Nat.not_even_iff_odd] at this
  · have := hcc q
    rw [show s(p, q) = s(q, p) from Sym2.eq_swap,
      jeb_jce_degree_insert_endpoint H.edgeSet q p hpq.symm hqp,
      jeb_jce_degree_eq_degree H hsub q] at this
    rwa [Nat.even_add_one, Nat.not_even_iff_odd] at this
  · intro v hvp hvq
    have := hcc v
    rwa [jeb_jce_degree_insert_other H.edgeSet p q v hvp hvq,
      jeb_jce_degree_eq_degree H hsub v] at this







theorem jeb_reachable_of_closedContour (H : SimpleGraph (Site 2))
    [SimpleGraph.LocallyFinite H] [Fintype H.edgeSet] (hsub : H ≤ hypercubicLattice 2)
    (p q : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hcc : jce_ClosedContour (insert (s(p,q)) H.edgeSet)) : H.Reachable p q := by
  obtain ⟨hp, hq, hother⟩ := jeb_degree_data_of_closedContour H hsub p q hpq hnpq hcc
  exact jeb_two_odd_reachable_of_edgeSet H p q hp hq hother











theorem jeb_contourSet_eq (H : SimpleGraph (Site 2)) [Fintype H.edgeSet] (p q f0 g0 : Site 2)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q)) :
    ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
      : Set (Sym2 (Site 2))) = insert (s(p, q)) H.edgeSet := by
  classical
  rw [Finset.coe_insert, Set.coe_toFinset, hshared]












theorem jeb_correctWhitney_of_evenDegree (H : SimpleGraph (Site 2))
    [SimpleGraph.LocallyFinite H] [Fintype H.edgeSet] (hsub : H ≤ hypercubicLattice 2)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    (H.Reachable p q ↔
      ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
  have hccSet : jce_ClosedContour (insert (s(p, q)) H.edgeSet) := by
    rwa [jeb_contourSet_eq H p q f0 g0 hshared] at hcc
  have hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
    jce_discreteJordanFaithful_of_evenDegree H p q f0 g0 hpq hnpq hfg hshared hcc
  have hreach : H.Reachable p q :=
    jeb_reachable_of_closedContour H hsub p q hpq hnpq hccSet
  exact ⟨fun _ => hsep, fun _ => hreach⟩










noncomputable instance jeb_imageGraph_locallyFinite (P : PlanarZ2Subgraph) :
    SimpleGraph.LocallyFinite (imageGraph P) := fun v =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun w hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (imageGraph_le_lattice P hw)))


theorem jeb_imageGraph_support_finite (P : PlanarZ2Subgraph) : (imageGraph P).support.Finite := by
  apply Set.Finite.subset (Set.finite_range P.emb)
  rintro v ⟨w, x, y, hadj, hx, hy⟩; exact ⟨x, hx⟩


noncomputable instance jeb_imageGraph_fintypeEdgeSet (P : PlanarZ2Subgraph) :
    Fintype (imageGraph P).edgeSet := by
  classical
  apply Set.Finite.fintype
  have hsupp := jeb_imageGraph_support_finite P
  apply Set.Finite.subset (s := (hsupp.toFinset.sym2 : Set (Sym2 (Site 2))))
  · exact (hsupp.toFinset.sym2).finite_toSet
  · rw [Finset.coe_sym2]
    exact (SimpleGraph.edgeSet_subset_sym2_iff).mpr
      (fun v hv => by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact hv)






theorem jeb_correctWhitney_imageGraph (P : PlanarZ2Subgraph)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ (imageGraph P).edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (imageGraph P).edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ((imageGraph P).Reachable p q ↔
      ¬ ((whb_faceRegion (imageGraph P)).deleteEdges {s(f0, g0)}).Reachable f0 g0) :=
  jeb_correctWhitney_of_evenDegree (imageGraph P) (imageGraph_le_lattice P) p q f0 g0
    hpq hnpq hfg hshared hcc























def jeb_EvenDegreeSubgraph (P : PlanarZ2Subgraph) : Prop :=
  jce_ClosedContour (imageGraph P).edgeSet









def jeb_FaithfulCountResidue : Prop :=
  ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → whc_FaithfulDiscreteJordan P




theorem jeb_faithfulDiscreteJordan_of_residue (hres : jeb_FaithfulCountResidue)
    (P : PlanarZ2Subgraph) (hP : jeb_EvenDegreeSubgraph P) :
    whc_FaithfulDiscreteJordan P :=
  hres P hP






theorem jeb_unitSquare_interior_bounded :
    Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} :=
  ⟨⟨(whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0],
    whb_faceRegion_interior_bounded⟩⟩













theorem jeb_Htest_le : whc_Htest ≤ hypercubicLattice 2 := fun a b hab =>
  imageGraph_le_lattice jbc_Pce (SimpleGraph.deleteEdges_le _ hab)


noncomputable instance jeb_Htest_locallyFinite : SimpleGraph.LocallyFinite whc_Htest := fun v =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun w hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (jeb_Htest_le hw)))


noncomputable instance jeb_Htest_fintypeEdgeSet : Fintype whc_Htest.edgeSet := by
  classical
  apply Set.Finite.fintype
  apply Set.Finite.subset (Set.toFinite (imageGraph jbc_Pce).edgeSet)
  exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _)




theorem jeb_square_closedContour : jce_ClosedContour (imageGraph jbc_Pce).edgeSet := by
  classical
  intro v
  rw [jce_degree, Finset.card_filter, Fin.sum_univ_four]
  simp only [jce_nbr, whc_square_mem_iff, Sym2.eq_iff, whc_site_eq_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  set x := v 0; set y := v 1
  by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;>
    (simp_all; try omega)


theorem jeb_Htest_insert_eq :
    insert (s(![(0:ℤ), 0], ![1, 0])) whc_Htest.edgeSet = (imageGraph jbc_Pce).edgeSet := by
  classical
  have hbot : s(![(0:ℤ), 0], ![1, 0]) ∈ (imageGraph jbc_Pce).edgeSet := by
    rw [whc_square_mem_iff]; tauto
  ext e
  rw [Set.mem_insert_iff, whc_Htest_mem]
  constructor
  · rintro (rfl | ⟨hsq, _⟩)
    · exact hbot
    · exact hsq
  · intro h
    by_cases hb : e = s(![(0:ℤ), 0], ![1, 0])
    · left; exact hb
    · right; exact ⟨h, hb⟩







theorem jeb_unitSquare_biconditional_fires :
    (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔
      ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable
        ![(0:ℤ), 0] ![(0:ℤ), -1]) := by
  have hpq : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hnpq : s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ whc_Htest.edgeSet := by
    rw [whc_Htest_mem]; push Not; intro _; rw [Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hshared : sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
    rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  have hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1]) whc_Htest.edgeSet.toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    classical
    rw [Finset.coe_insert, Set.coe_toFinset, hshared, jeb_Htest_insert_eq]
    exact jeb_square_closedContour
  exact jeb_correctWhitney_of_evenDegree whc_Htest jeb_Htest_le
    ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1] hpq hnpq hfg hshared hcc

end Lattice

end StatMech
