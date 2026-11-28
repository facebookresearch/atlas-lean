/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.SymmDiff
public import MathlibExt.Combinatorics.Matching.BergeLemma
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Chain

/-!
# Augmenting paths from components of two matchings

Berge's lemma supplies an augmenting path in any connected component with more edges of the
second matching than of the first. Counting these components gives Hopcroft and Karp's
disjoint augmenting paths in the symmetric difference and their short augmenting path bound.
-/

public section

namespace MetaMathlibExt

open SimpleGraph
open scoped symmDiff

/-- Each component with a surplus contributes at most one to the total excess. -/
private lemma excess_le_card_pos {ι : Type*} [Fintype ι] (m n : ι → ℕ)
    [DecidablePred (fun i => m i < n i)] (h : ∀ i, n i ≤ m i + 1) :
    (∑ i, n i) ≤ (∑ i, m i) + (Finset.univ.filter (fun i => m i < n i)).card := by
  calc
    (∑ i, n i) ≤ ∑ i, (m i + if m i < n i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact h i
      · omega
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole]

/-- Some component with a surplus contains at most the indicated share of the smaller matching. -/
private lemma exists_small_component {ι : Type*} [Fintype ι] (m n : ι → ℕ) {r s : ℕ}
    (hm : ∑ i, m i = r) (hn : ∑ i, n i = s) (hlt : r < s) (h : ∀ i, n i ≤ m i + 1) :
    ∃ i, m i < n i ∧ m i ≤ r / (s - r) := by
  classical
  let P := Finset.univ.filter (fun i => m i < n i)
  have hnum : s ≤ r + P.card := by simpa only [hm, hn] using excess_le_card_pos m n h
  by_contra! hlarge
  let k := r / (s - r) + 1
  have hcost : k * (s - r) ≤ r := calc
    k * (s - r) ≤ k * P.card := Nat.mul_le_mul_left _ (by omega)
    _ = ∑ _i ∈ P, k := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ P, m i := Finset.sum_le_sum fun i hi =>
      hlarge i (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, m i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = r := hm
  exact (Nat.div_lt_iff_lt_mul (by omega : 0 < s - r)).mp (Nat.lt_succ_self _) |>.not_ge hcost

private noncomputable def edgeComponent {V : Type*} (H : SimpleGraph V) (e : Sym2 V) :
    H.ConnectedComponent := H.connectedComponentMk e.out.1

/-- The component of an edge can be read off at either endpoint. -/
private lemma component_at_endpoint {V : Type*} {H : SimpleGraph V} {e : Sym2 V}
    (he : e ∈ H.edgeSet) {x : V} (hx : x ∈ e) :
    H.connectedComponentMk x = edgeComponent H e := by
  change H.connectedComponentMk x = H.connectedComponentMk e.out.1
  by_cases h : x = e.out.1
  · rw [h]
  · have hadj : H.Adj x e.out.1 := by
      rwa [← mem_edgeSet, ← (Sym2.mem_and_mem_iff h).mp ⟨hx, e.out_fst_mem⟩]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-- A matching in a vertex set uses two distinct vertices for each edge. -/
private lemma twice_card_matching_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (B : Finset (Sym2 V)) (S : Finset V) (hG : ∀ e ∈ B, e ∈ G.edgeSet)
    (hB : ∀ e₁ ∈ B, ∀ e₂ ∈ B, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hS : ∀ e ∈ B, e.toFinset ⊆ S) : 2 * B.card ≤ S.card := by
  have hd : (B : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro a ha b hb hne
    exact Finset.disjoint_left.mpr fun x hx hy =>
      hB a ha b hb hne x (Sym2.mem_toFinset.mp hx) (Sym2.mem_toFinset.mp hy)
  calc
    2 * B.card = ∑ e ∈ B, e.toFinset.card := by
      rw [Finset.sum_const_nat (m := 2), Nat.mul_comm]
      exact fun e he => e.card_toFinset_of_not_isDiag (G.not_isDiag_of_mem_edgeSet (hG e he))
    _ = (B.biUnion Sym2.toFinset).card := (Finset.card_biUnion hd).symm
    _ ≤ S.card := Finset.card_le_card (Finset.biUnion_subset.mpr hS)

/-- Build the graph on a set of genuine edges, keeping the ambient vertex type. -/
private lemma edgeSet_fromFinset_of_subset {V : Type*} (G : SimpleGraph V)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet) :
    (fromEdgeSet (E : Set (Sym2 V))).edgeSet = E := by
  rw [edgeSet_fromEdgeSet]
  ext e
  exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (hE e he)⟩⟩

private noncomputable def componentEdges {V : Type*} (H : SimpleGraph V)
    [DecidableEq H.ConnectedComponent]
    (E : Finset (Sym2 V)) (c : H.ConnectedComponent) : Finset (Sym2 V) :=
  E.filter (edgeComponent H · = c)

private lemma sum_card_componentEdges {V : Type*} (H : SimpleGraph V)
    [Fintype H.ConnectedComponent] [DecidableEq H.ConnectedComponent] (E : Finset (Sym2 V)) :
    ∑ c, (componentEdges H E c).card = E.card :=
  (Finset.card_eq_sum_card_fiberwise (f := edgeComponent H) (fun _ _ => Finset.mem_univ _)).symm

/-- Connectivity gives `|V(c)| ≤ |E(c)| + 1`, while the edges of the second matching use two
vertices each. Thus that matching has at most one more edge in the component. -/
private lemma component_card_le_add_one {V : Type*} [Finite V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableEq H.ConnectedComponent] (A B : Finset (Sym2 V))
    (hH : H.edgeSet = ↑(A ∪ B))
    (hB : ∀ e₁ ∈ B, ∀ e₂ ∈ B, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (c : H.ConnectedComponent) : (componentEdges H B c).card ≤ (componentEdges H A c).card + 1 := by
  classical
  let := Fintype.ofFinite V
  let : Fintype H.edgeSet := H.fintypeEdgeSet
  let S := c.supp.toFinset
  have inside {e : Sym2 V} (he : e ∈ A ∪ B) :
      e.toFinset ⊆ S ↔ edgeComponent H e = c := by
    refine ⟨fun h => Set.mem_toFinset.mp (h (Sym2.mem_toFinset.mpr e.out_fst_mem)), ?_⟩
    intro hc x hx
    exact Set.mem_toFinset.mpr
      ((component_at_endpoint (hH ▸ he) (Sym2.mem_toFinset.mp hx)).trans hc)
  have hvertices : 2 * (componentEdges H B c).card ≤ S.card := by
    apply twice_card_matching_le H
    · exact fun e he => hH ▸ Finset.mem_union_right A (Finset.mem_filter.mp he).1
    · exact fun a ha b hb => hB a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    · intro e he
      obtain ⟨heB, hc⟩ := Finset.mem_filter.mp he
      exact (inside (Finset.mem_union_right A heB)).mpr hc
  have hpart : H.edgeFinset.filter (fun e => e.toFinset ⊆ S) =
      componentEdges H A c ∪ componentEdges H B c := by
    rw [componentEdges, componentEdges, ← Finset.filter_union]
    have heq : H.edgeFinset = A ∪ B := by ext; simp [hH]
    rw [heq]
    exact Finset.filter_congr fun e he => inside he
  have hcard := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have heq : (componentEdges H A c ∪ componentEdges H B c).card =
      Nat.card c.toSimpleGraph.edgeSet := by
    rw [← hpart]
    calc
      _ = (H.induce (S : Set V)).edgeFinset.card :=
        card_filter_edgeFinset_toFinset_subset (G := H) S
      _ = Nat.card (H.induce (S : Set V)).edgeSet :=
        edgeFinset_card.trans Nat.card_eq_fintype_card.symm
      _ = Nat.card c.toSimpleGraph.edgeSet :=
        congrArg (fun T : Set V => Nat.card (H.induce T).edgeSet) (Set.coe_toFinset _)
  rw [← heq] at hcard
  have hs : S.card = Nat.card c := by simp [S, ← Nat.card_eq_fintype_card]
  have := Finset.card_union_le (componentEdges H A c) (componentEdges H B c)
  omega

/-- Apply Berge's lemma to the edges in one component. The incidence condition ensures
that exposed endpoints there are also exposed in the original matching. -/
private lemma augment_in_component {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (M A B : Finset (Sym2 V))
    (hG : ∀ e ∈ A ∪ B, e ∈ G.edgeSet)
    (hA : ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hB : ∀ e₁ ∈ B, ∀ e₂ ∈ B, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hAM : A ⊆ M) (hlocal : ∀ e ∈ M, ∀ f ∈ A ∪ B, ∀ x : V, x ∈ e → x ∈ f → e ∈ A)
    (hlt : A.card < B.card) :
    ∃ (u v : V) (p : G.Walk u v), IsAugmentingWalk M p ∧
      p.length ≤ A.card + B.card ∧ ∀ e ∈ p.edges, e ∈ A ∪ B := by
  classical
  let := Fintype.ofFinite V
  let K := fromEdgeSet ((A ∪ B : Finset _) : Set (Sym2 V))
  have hK : K.edgeSet = A ∪ B := edgeSet_fromFinset_of_subset G _ hG
  have hle : K ≤ G := edgeSet_subset_edgeSet.mp (by rw [hK]; exact fun _ he => hG _ he)
  have hAK : ∀ e ∈ A, e ∈ K.edgeSet := fun e he => hK ▸ Finset.mem_union_left B he
  have hBK : ∀ e ∈ B, e ∈ K.edgeSet := fun e he => hK ▸ Finset.mem_union_right A he
  obtain ⟨u, v, p, hp⟩ : ∃ (u v : V) (p : K.Walk u v), IsAugmentingWalk A p := by
    by_contra h
    exact hlt.not_ge (((berge_iff_not_exists_isAugmentingWalk K A hAK hA).mpr h) B hBK hB)
  obtain ⟨hne, hnodup, hu, hv, hchain, hpos⟩ := hp
  have hedges {e} (he : e ∈ p.edges) : e ∈ A ∪ B := by
    have := p.edges_subset_edgeSet he
    rwa [hK] at this
  have exposed (x : V) (hx : x ∈ p.support) (h : ∀ e ∈ A, x ∉ e) : ∀ e ∈ M, x ∉ e := by
    obtain ⟨f, hf, hxf⟩ :=
      (Walk.mem_support_iff_exists_mem_edges_of_not_nil (Walk.not_nil_of_ne hne)).mp hx
    exact fun e he hxe => h e (hlocal e he f (hedges hf) x hxe hxf) hxe
  have mem_iff (e : Sym2 V) (he : e ∈ p.edges) : e ∈ A ↔ e ∈ M :=
    ⟨fun h => hAM h, fun h => hlocal e h e (hedges he) _ e.out_fst_mem e.out_fst_mem⟩
  refine ⟨u, v, p.mapLe hle, ?_, ?_, ?_⟩
  · simp only [IsAugmentingWalk, Walk.support_mapLe_eq_support, Walk.edges_mapLe_eq_edges,
      Walk.length_mapLe]
    refine ⟨hne, hnodup, exposed u p.start_mem_support hu, exposed v p.end_mem_support hv,
      ?_, hpos⟩
    exact hchain.imp_of_mem_imp fun a b ha hb hab => by
      simpa only [mem_iff a ha, mem_iff b hb] using hab
  · rw [Walk.length_mapLe, ← Walk.length_edges, ← List.toFinset_card_of_nodup
      (Walk.edges_nodup_of_support_nodup hnodup)]
    exact (Finset.card_le_card fun e he => hedges (List.mem_toFinset.mp he)).trans
      (Finset.card_union_le A B)
  · simpa only [Walk.edges_mapLe_eq_edges] using (fun e he => hedges (e := e) he)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **A short augmenting path exists (Hopcroft–Karp, Corollary 2).** Let `M` and `N` be matchings
of a finite simple graph `G` with `|M| = r < |N|`. Then some `M`-augmenting walk has length at
most `2 ⌊r / (|N| - r)⌋ + 1` (Hopcroft and Karp, SIAM J. Comput. 2 (1973), §2, Corollary 2,
stated there with `|N| = s` the maximum matching size; taking `N` maximum recovers it, and the
proof there works for any larger matching `N`). -/
theorem exists_isAugmentingWalk_length_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M N : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hN : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hlt : M.card < N.card) :
    ∃ (u v : V) (p : G.Walk u v), IsAugmentingWalk M p ∧
      p.length ≤ 2 * (M.card / (N.card - M.card)) + 1 := by
  classical
  let H := fromEdgeSet ((M ∪ N : Finset _) : Set (Sym2 V))
  have hG : ∀ e ∈ M ∪ N, e ∈ G.edgeSet := fun e he =>
    (Finset.mem_union.mp he).elim (hMG e) (hNG e)
  have hH : H.edgeSet = ↑(M ∪ N) := edgeSet_fromFinset_of_subset G _ hG
  let part := componentEdges H
  have endpoint {e : Sym2 V} (he : e ∈ M ∪ N) {x : V} (hx : x ∈ e) :
      H.connectedComponentMk x = edgeComponent H e :=
    component_at_endpoint (hH ▸ he) hx
  have surplus := component_card_le_add_one H M N hH hN
  obtain ⟨c, hc, hsmall⟩ := exists_small_component _ _ (sum_card_componentEdges H M)
    (sum_card_componentEdges H N) hlt surplus
  have hsub : part M c ∪ part N c ⊆ M ∪ N :=
    Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  obtain ⟨u, v, p, hp, hlen, _⟩ := augment_in_component G M (part M c) (part N c)
    (fun e he => hG e (hsub he))
    (fun a ha b hb => hM a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
    (fun a ha b hb => hN a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
    (Finset.filter_subset _ _) (by
      intro e he f hf x hxe hxf
      have hf' : edgeComponent H f = c := (Finset.mem_union.mp hf).elim
        (fun h => (Finset.mem_filter.mp h).2) (fun h => (Finset.mem_filter.mp h).2)
      exact Finset.mem_filter.mpr ⟨he, (endpoint (Finset.mem_union_left N he) hxe).symm.trans
        ((endpoint (hsub hf) hxf).trans hf')⟩) hc
  dsimp only [part] at hlen
  have := surplus c
  exact ⟨u, v, p, hp, by omega⟩

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1).** Let `M`
and `N` be matchings of a finite simple graph `G`. Then there are `|N| - |M|` pairwise
vertex-disjoint `M`-augmenting walks whose edges all lie in `M ⊕ N` (Hopcroft and Karp, SIAM J.
Comput. 2 (1973), §2, Theorem 1, stated there for `|N| > |M|`; when `|N| ≤ |M|` the truncated
difference is `0` and the statement is empty). -/
theorem exists_disjoint_augmentingWalks {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (M N : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hN : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) :
    ∃ P : Fin (N.card - M.card) → (u : V) × (v : V) × G.Walk u v,
      (∀ i, IsAugmentingWalk M (P i).2.2 ∧ ∀ e ∈ (P i).2.2.edges, e ∈ M ∆ N) ∧
        ∀ i j, i ≠ j → List.Disjoint (P i).2.2.support (P j).2.2.support := by
  by_cases hle : N.card ≤ M.card
  · rw [Nat.sub_eq_zero_of_le hle]
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  classical
  let A := M \ N
  let B := N \ M
  let H := fromEdgeSet ((A ∪ B : Finset _) : Set (Sym2 V))
  let part := componentEdges H
  have hG : ∀ e ∈ A ∪ B, e ∈ G.edgeSet := fun e he =>
    (Finset.mem_union.mp he).elim (fun ha => hMG e (Finset.mem_sdiff.mp ha).1)
      (fun hb => hNG e (Finset.mem_sdiff.mp hb).1)
  have hH : H.edgeSet = ↑(A ∪ B) := edgeSet_fromFinset_of_subset G _ hG
  have hB : ∀ e₁ ∈ B, ∀ e₂ ∈ B, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂ :=
    fun a ha b hb => hN a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  let m (c : H.ConnectedComponent) := (part A c).card
  let n (c : H.ConnectedComponent) := (part B c).card
  let positive := Finset.univ.filter (fun c => m c < n c)
  have hnum : N.card - M.card ≤ positive.card := by
    have hsum := excess_le_card_pos m n (component_card_le_add_one H A B hH hB)
    change (∑ c, (part B c).card) ≤ (∑ c, (part A c).card) + positive.card at hsum
    rw [sum_card_componentEdges H B, sum_card_componentEdges H A] at hsum
    have ha : A.card + (M ∩ N).card = M.card := Finset.card_sdiff_add_card_inter M N
    have hb : B.card + (M ∩ N).card = N.card := by
      rw [Finset.inter_comm M N]
      exact Finset.card_sdiff_add_card_inter N M
    omega
  let pick : Fin (N.card - M.card) ↪ ↥positive :=
    (Fin.castLEEmb hnum).trans positive.equivFin.symm.toEmbedding
  have pathInComponent (c : ↥positive) :
      ∃ (u v : V) (p : G.Walk u v), IsAugmentingWalk M p ∧
        (∀ e ∈ p.edges, e ∈ M ∆ N) ∧ ∀ x ∈ p.support, H.connectedComponentMk x = c.val := by
    have hc : m c.val < n c.val := (Finset.mem_filter.mp c.property).2
    have hsub : part A c.val ∪ part B c.val ⊆ A ∪ B :=
      Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcomponent {f : Sym2 V} (hf : f ∈ part A c.val ∪ part B c.val) {x : V} (hx : x ∈ f) :
        H.connectedComponentMk x = c.val :=
      (component_at_endpoint (hH ▸ hsub hf) hx).trans ((Finset.mem_union.mp hf).elim
        (fun h => (Finset.mem_filter.mp h).2) (fun h => (Finset.mem_filter.mp h).2))
    have hlocal (e : Sym2 V) (he : e ∈ M) (f : Sym2 V)
        (hf : f ∈ part A c.val ∪ part B c.val) (x : V) (hxe : x ∈ e) (hxf : x ∈ f) :
        e ∈ part A c.val := by
      -- A common edge cannot meet any edge of the symmetric difference.
      have heA : e ∈ A := Finset.mem_sdiff.mpr ⟨he, fun hen => by
        rcases Finset.mem_union.mp (hsub hf) with hfA | hfB
        · have hef : e = f := by
            by_contra hne
            exact hM e he f (Finset.mem_sdiff.mp hfA).1 hne x hxe hxf
          exact (Finset.mem_sdiff.mp hfA).2 (hef ▸ hen)
        · have hef : e = f := by
            by_contra hne
            exact hN e hen f (Finset.mem_sdiff.mp hfB).1 hne x hxe hxf
          exact (Finset.mem_sdiff.mp hfB).2 (hef ▸ he)⟩
      exact Finset.mem_filter.mpr ⟨heA,
        (component_at_endpoint (hH ▸ Finset.mem_union_left B heA) hxe).symm.trans
          (hcomponent hf hxf)⟩
    obtain ⟨u, v, p, hp, _, hedges⟩ := augment_in_component G M (part A c.val) (part B c.val)
      (fun e he => hG e (hsub he))
      (fun a ha b hb => hM a (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
        b (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1)
      (fun a ha b hb => hB a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
      ((Finset.filter_subset _ _).trans Finset.sdiff_subset) hlocal hc
    refine ⟨u, v, p, hp, ?_, ?_⟩
    · intro e he
      rw [Finset.symmDiff_def]
      exact hsub (hedges e he)
    · intro x hx
      obtain ⟨e, he, hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (Walk.not_nil_of_ne hp.1)).mp hx
      exact hcomponent (hedges e he) hxe
  choose u v p hp hedges hsupport using pathInComponent
  refine ⟨fun i => ⟨u (pick i), v (pick i), p (pick i)⟩, fun i => ⟨hp _, hedges _⟩, ?_⟩
  intro i j hij
  exact List.disjoint_left.mpr fun x hxi hxj =>
    hij (pick.injective (Subtype.ext ((hsupport _ x hxi).symm.trans (hsupport _ x hxj))))

end MetaMathlibExt
