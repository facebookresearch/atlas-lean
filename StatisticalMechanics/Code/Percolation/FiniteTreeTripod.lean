/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Mathlib

open Set SimpleGraph Finset

namespace StatMech.Percolation


theorem ftt_tree_two_leaves {V : Type*} [Fintype V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
  classical
  have hNontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have hpos : ∀ v : V, 1 ≤ T.degree v := by
    intro v
    have := hT.connected.preconnected.minDegree_pos_of_nontrivial (G := T)
    exact le_trans this (T.minDegree_le_degree v)
  have hsum : ∑ v : V, T.degree v = 2 * #T.edgeFinset :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : #T.edgeFinset + 1 = Fintype.card V := hT.card_edgeFinset
  by_contra hcon
  push Not at hcon
  have hleaf_sub : ∀ a b : V, T.degree a = 1 → T.degree b = 1 → a = b := by
    intro a b ha hb
    by_contra hab
    exact hcon a b hab ha hb
  obtain ⟨v0, hv0⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hlower : 2 * Fintype.card V - 1 ≤ ∑ v : V, T.degree v := by
    have hbound : ∀ v : V, (if v = v0 then 1 else 2) ≤ T.degree v := by
      intro v
      by_cases hvv : v = v0
      . subst hvv
        simp [hv0]
      . simp only [if_neg hvv]
        rcases Nat.lt_or_ge (T.degree v) 2 with hlt | hge
        . have h1 : T.degree v = 1 := by have := hpos v; omega
          exact absurd (hleaf_sub v v0 h1 hv0) hvv
        . exact hge
    have hconst : (∑ v : V, if v = v0 then (1 : ℕ) else 2) + 1 =
        2 * Fintype.card V := by
      have hstep : (∑ v : V, (if v = v0 then (1 : ℕ) else 2)) + 1 =
          ∑ v : V, ((if v = v0 then (1 : ℕ) else 2) +
            (if v = v0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v0]
        simp
      rw [hstep]
      have htwo : ∀ v : V,
          (if v = v0 then (1 : ℕ) else 2) + (if v = v0 then 1 else 0) = 2 := by
        intro v
        by_cases hvv : v = v0 <;> simp [hvv]
      rw [Finset.sum_congr rfl (fun v _ => htwo v), Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_comm]
    have hsumif : (∑ v : V, (if v = v0 then (1 : ℕ) else 2)) ≤
        ∑ v : V, T.degree v :=
      Finset.sum_le_sum (fun v _ => hbound v)
    omega
  omega


theorem ftt_branch_vertex_of_three_leaves {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : T.degree a = 1) (hb : T.degree b = 1) (hc : T.degree c = 1) :
    ∃ u : V, 3 ≤ T.degree u := by
  classical
  by_contra hbranch
  push Not at hbranch
  let L : Finset V := {a, b, c}
  have hLcard : L.card = 3 := by simp [L, hab, hac, hbc]
  have hbound : ∀ v : V,
      T.degree v + (if v ∈ L then 1 else 0) ≤ 2 := by
    intro v
    by_cases hv : v ∈ L
    · simp only [L, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · simp [L, ha]
      · simp [L, hb]
      · simp [L, hc]
    · simp only [if_neg hv, add_zero]
      have := hbranch v
      omega
  have hsum_bound :
      (∑ v : V, (T.degree v + (if v ∈ L then 1 else 0))) ≤
        ∑ _v : V, 2 :=
    Finset.sum_le_sum (fun v _ => hbound v)
  have hind : (∑ v : V, if v ∈ L then 1 else 0) = L.card := by
    rw [Finset.sum_boole]
    simp
  have hdeg : ∑ v : V, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have htwoSum : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib, hind, hLcard, hdeg, htwoSum, ← hedge] at hsum_bound
  omega


theorem ftt_not_mem_support_of_isolated {V : Type*} {G : SimpleGraph V} {u : V}
    (hiso : ∀ z, ¬ G.Adj u z) : ∀ {a b : V} (w : G.Walk a b), a ≠ u → u ∉ w.support := by
  intro a b w
  induction w with
  | nil => intro ha; simpa using ha.symm
  | @cons a v b hav w ih =>
      intro ha
      have hv : v ≠ u := fun hvu => hiso a (hvu ▸ hav.symm)
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun h => ha h.symm, ih hv⟩



theorem ftt_neighbors_separated {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b) :
    ¬ (G.deleteIncidenceSet u).Reachable a b := by
  classical
  rintro ⟨w⟩
  have hle : G.deleteIncidenceSet u ≤ G := G.deleteIncidenceSet_le u
  have hiso : ∀ z, ¬ (G.deleteIncidenceSet u).Adj u z :=
    fun z h => (deleteIncidenceSet_adj.mp h).2.1 rfl
  have hnotin : u ∉ w.support :=
    ftt_not_mem_support_of_isolated hiso w hua.symm.ne
  have hnotin_map : u ∉ (w.mapLe hle).support := by
    rw [Walk.support_mapLe_eq_support hle w]
    exact hnotin
  set p : G.Path a b := (w.mapLe hle).toPath
  have hp_notin : u ∉ p.1.support := by
    intro hu
    exact hnotin_map (Walk.support_toPath_subset _ hu)
  have hbne : u ≠ b := hub.ne
  have haune : a ≠ u := hua.symm.ne
  have qpath : (Walk.cons hua.symm (Walk.cons hub Walk.nil)).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    . simpa using hbne
    . simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, not_or]
      exact ⟨haune, hab, by simp⟩
  set q : G.Path a b := ⟨_, qpath⟩
  have hq_in : u ∈ q.1.support := by
    simp [q]
  have huniq := hG.path_unique p q
  rw [huniq] at hp_notin
  exact hp_notin hq_in


theorem ftt_leaf_in_neighbor_branch {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {u v : V}
    (huv : T.Adj u v) :
    ∃ l : V, T.degree l = 1 ∧ (T.deleteIncidenceSet u).Reachable v l := by
  classical
  let H := T.deleteIncidenceSet u
  let C : Set V := {x | H.Reachable v x}
  let K : SimpleGraph C := H.induce C
  have hvu : v ≠ u := huv.ne'
  have hu_not_C : u ∉ C := by
    intro huC
    have hr : H.Reachable v u := huC
    obtain ⟨p⟩ := hr
    have hiso : ∀ z, ¬ H.Adj u z :=
      fun z h => (deleteIncidenceSet_adj.mp h).2.1 rfl
    exact (ftt_not_mem_support_of_isolated hiso p hvu) (by simp)
  have hKconn : K.Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨v, Reachable.refl v⟩⟩
    intro a b
    have hav : H.Reachable v a := a.2
    have hbv : H.Reachable v b := b.2
    obtain ⟨pa⟩ := hav
    obtain ⟨pb⟩ := hbv
    let q := pa.reverse.append pb
    have hqC : ∀ x ∈ q.support, x ∈ C := by
      intro x hx
      exact ⟨pa.append (q.takeUntil x hx)⟩
    exact ⟨q.induce C hqC⟩
  have hKacyc : K.IsAcyclic :=
    (hT.isAcyclic.anti (T.deleteIncidenceSet_le u)).induce C
  have hKtree : K.IsTree := ⟨hKconn, hKacyc⟩
  have hCclosed : ∀ {x y : V}, H.Adj x y → x ∈ C → y ∈ C := by
    intro x y hxy hx
    exact hx.trans hxy.reachable
  have hKdegree (x : C) : K.degree x = H.degree x.1 := by
    change (H.induce C).degree x = H.degree x.1
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro y hy
    exact hCclosed (SimpleGraph.mem_neighborSet H x.1 y |>.mp hy) x.2
  by_cases hcard : Fintype.card C = 1
  . refine ⟨v, ?_, Reachable.refl v⟩
    rw [degree_eq_one_iff_existsUnique_adj]
    refine ⟨u, huv.symm, ?_⟩
    intro z hvz
    by_cases hzu : z = u
    . exact hzu
    . have hvzH : H.Adj v z := deleteIncidenceSet_adj.mpr ⟨hvz, hvu, hzu⟩
      have hzC : z ∈ C := hvzH.reachable
      have hsub : Subsingleton C := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have : (z : V) = v := congrArg Subtype.val
        (hsub.elim ⟨z, hzC⟩ ⟨v, Reachable.refl v⟩)
      exact absurd this hvz.ne'
  . have hcard2 : 2 ≤ Fintype.card C := by
      have hpos : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨v, Reachable.refl v⟩
      omega
    obtain ⟨a, b, hab, ha, hb⟩ := ftt_tree_two_leaves K hKtree hcard2
    have hchoice : ∃ l : C, l.1 ≠ v ∧ K.degree l = 1 := by
      by_cases hav : a.1 = v
      . refine ⟨b, ?_, hb⟩
        intro hbv
        exact hab (Subtype.ext (hav.trans hbv.symm))
      . exact ⟨a, hav, ha⟩
    obtain ⟨l, hlv, hlK⟩ := hchoice
    have hlu : l.1 ≠ u := fun h => hu_not_C (h ▸ l.2)
    have hnotadj_u : ¬ T.Adj u l.1 := by
      intro hul
      exact ftt_neighbors_separated T hT.isAcyclic huv hul (fun h => hlv h.symm) l.2
    have hlH : H.degree l.1 = 1 := by
      rw [← hKdegree l]
      exact hlK
    have hlT : T.degree l.1 = 1 := by
      rw [degree_eq_one_iff_existsUnique_adj] at hlH ⊢
      obtain ⟨z, hlz, hzuniq⟩ := hlH
      refine ⟨z, (deleteIncidenceSet_adj.mp hlz).1, ?_⟩
      intro z' hlz'
      have hz'u : z' ≠ u := by
        intro h
        subst z'
        exact hnotadj_u hlz'.symm
      exact hzuniq z' (deleteIncidenceSet_adj.mpr ⟨hlz', hlu, hz'u⟩)
    exact ⟨l.1, hlT, l.2⟩



theorem ftt_finite_tree_tripod {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {u : V}
    (hu : 3 ≤ T.degree u) :
    ∃ l : Fin 3 → V,
      Function.Injective l ∧
      (∀ i, T.degree (l i) = 1) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet u).Reachable (l i) (l j)) := by
  classical
  have hcard : Fintype.card (Fin 3) ≤
      Fintype.card {x // x ∈ T.neighborFinset u} := by
    rw [Fintype.card_fin, Fintype.card_coe,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  obtain ⟨n⟩ : Nonempty (Fin 3 ↪ {x // x ∈ T.neighborFinset u}) :=
    Function.Embedding.nonempty_iff_card_le.mpr hcard
  let v : Fin 3 → V := fun i => (n i).1
  have hvadj : ∀ i, T.Adj u (v i) := fun i =>
    (SimpleGraph.mem_neighborFinset T u (v i)).mp (n i).2
  have hvinj : Function.Injective v := fun i j hij => n.injective (Subtype.ext hij)
  choose l hleaf hreach using fun i => ftt_leaf_in_neighbor_branch T hT (hvadj i)
  have hsep : ∀ i j, i ≠ j →
      ¬ (T.deleteIncidenceSet u).Reachable (l i) (l j) := by
    intro i j hij hlij
    have hvne : v i ≠ v j := fun h => hij (hvinj h)
    have hvreach : (T.deleteIncidenceSet u).Reachable (v i) (v j) :=
      (hreach i).trans (hlij.trans (hreach j).symm)
    exact ftt_neighbors_separated T hT.isAcyclic (hvadj i) (hvadj j) hvne hvreach
  have hlinj : Function.Injective l := by
    intro i j hij
    by_contra hne
    exact hsep i j hne (hij ▸ Reachable.refl (l i))
  exact ⟨l, hlinj, hleaf, hsep⟩



theorem ftt_finite_tree_tripod_with_stems {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {u : V}
    (hu : 3 ≤ T.degree u) :
    ∃ stem leaf : Fin 3 → V,
      Function.Injective stem ∧
      (∀ i, T.Adj u (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, T.degree (leaf i) = 1) ∧
      (∀ i, (T.deleteIncidenceSet u).Reachable (stem i) (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet u).Reachable (leaf i) (leaf j)) := by
  classical
  have hcard : Fintype.card (Fin 3) ≤
      Fintype.card {x // x ∈ T.neighborFinset u} := by
    rw [Fintype.card_fin, Fintype.card_coe,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  obtain ⟨n⟩ : Nonempty (Fin 3 ↪ {x // x ∈ T.neighborFinset u}) :=
    Function.Embedding.nonempty_iff_card_le.mpr hcard
  let stem : Fin 3 → V := fun i => (n i).1
  have hstemAdj : ∀ i, T.Adj u (stem i) := fun i =>
    (SimpleGraph.mem_neighborFinset T u (stem i)).mp (n i).2
  have hstemInj : Function.Injective stem := fun i j hij =>
    n.injective (Subtype.ext hij)
  choose leaf hleaf hreach using fun i =>
    ftt_leaf_in_neighbor_branch T hT (hstemAdj i)
  have hsep : ∀ i j, i ≠ j →
      ¬ (T.deleteIncidenceSet u).Reachable (leaf i) (leaf j) := by
    intro i j hij hlij
    have hstemNe : stem i ≠ stem j := fun h => hij (hstemInj h)
    have hr : (T.deleteIncidenceSet u).Reachable (stem i) (stem j) :=
      (hreach i).trans (hlij.trans (hreach j).symm)
    exact ftt_neighbors_separated T hT.isAcyclic
      (hstemAdj i) (hstemAdj j) hstemNe hr
  have hleafInj : Function.Injective leaf := by
    intro i j hij
    by_contra hne
    exact hsep i j hne (hij ▸ Reachable.refl (leaf i))
  exact ⟨stem, leaf, hstemInj, hstemAdj, hleafInj, hleaf, hreach, hsep⟩

end StatMech.Percolation
