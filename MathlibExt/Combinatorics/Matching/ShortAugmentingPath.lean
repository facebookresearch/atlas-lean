/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.BergeLemma
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Chain

/-!
# Short augmenting paths

Hopcroft and Karp's bound on the length of an augmenting path follows by applying Berge's
lemma in a connected component of the union of two matchings.
-/

public section

namespace MetaMathlibExt

open SimpleGraph

/-- Each component with a surplus contributes at most one to the total excess. Among those
components at least one has at most the indicated share of the smaller matching. -/
private lemma exists_small_component {ι : Type*} [Fintype ι] (m n : ι → ℕ) {r s : ℕ}
    (hm : ∑ i, m i = r) (hn : ∑ i, n i = s) (hlt : r < s) (h : ∀ i, n i ≤ m i + 1) :
    ∃ i, m i < n i ∧ m i ≤ r / (s - r) := by
  classical
  let P := Finset.univ.filter (fun i => m i < n i)
  have hnum : s ≤ r + P.card := calc
    s = ∑ i, n i := hn.symm
    _ ≤ ∑ i, (m i + if m i < n i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact h i
      · omega
    _ = r + P.card := by simp [Finset.sum_add_distrib, hm, Finset.sum_boole, P]
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

/-- The component of an edge can be read off at either endpoint. -/
private lemma component_at_endpoint {V : Type*} {H : SimpleGraph V} {e : Sym2 V}
    (he : e ∈ H.edgeSet) {x : V} (hx : x ∈ e) :
    H.connectedComponentMk x = H.connectedComponentMk e.out.1 := by
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

/-- Apply Berge's lemma to the edges in one component. The incidence condition ensures
that exposed endpoints there are also exposed in the original matching. -/
private lemma augment_in_component {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (M A B : Finset (Sym2 V))
    (hG : ∀ e ∈ A ∪ B, e ∈ G.edgeSet)
    (hA : ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hB : ∀ e₁ ∈ B, ∀ e₂ ∈ B, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hAM : A ⊆ M) (hlocal : ∀ e ∈ M, ∀ f ∈ A ∪ B, ∀ x : V, x ∈ e → x ∈ f → e ∈ A)
    (hlt : A.card < B.card) :
    ∃ (u v : V) (p : G.Walk u v), IsAugmentingWalk M p ∧ p.length ≤ A.card + B.card := by
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
  refine ⟨u, v, p.mapLe hle, ?_, ?_⟩
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
  let : Fintype H.edgeSet := H.fintypeEdgeSet
  have hG : ∀ e ∈ M ∪ N, e ∈ G.edgeSet := fun e he =>
    (Finset.mem_union.mp he).elim (hMG e) (hNG e)
  have hH : H.edgeSet = ↑(M ∪ N) := edgeSet_fromFinset_of_subset G _ hG
  let comp (e : Sym2 V) := H.connectedComponentMk e.out.1
  let part (E : Finset (Sym2 V)) (c : H.ConnectedComponent) := E.filter (comp · = c)
  have sum_part (E : Finset (Sym2 V)) : ∑ c, (part E c).card = E.card :=
    (Finset.card_eq_sum_card_fiberwise (f := comp) (fun _ _ => Finset.mem_univ _)).symm
  have endpoint {e : Sym2 V} (he : e ∈ M ∪ N) {x : V} (hx : x ∈ e) :
      H.connectedComponentMk x = comp e :=
    component_at_endpoint (hH ▸ he) hx
  have surplus (c : H.ConnectedComponent) : (part N c).card ≤ (part M c).card + 1 := by
    let S := c.supp.toFinset
    have inside {e : Sym2 V} (he : e ∈ M ∪ N) :
        e.toFinset ⊆ S ↔ comp e = c := by
      refine ⟨fun h => Set.mem_toFinset.mp (h (Sym2.mem_toFinset.mpr e.out_fst_mem)), ?_⟩
      intro hc x hx
      exact Set.mem_toFinset.mpr ((endpoint he (Sym2.mem_toFinset.mp hx)).trans hc)
    have hvertices : 2 * (part N c).card ≤ S.card := by
      apply twice_card_matching_le G
      · exact fun e he => hNG e (Finset.mem_filter.mp he).1
      · exact fun a ha b hb => hN a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      · intro e he
        obtain ⟨heN, hc⟩ := Finset.mem_filter.mp he
        exact (inside (Finset.mem_union_right M heN)).mpr hc
    have hpart : H.edgeFinset.filter (fun e => e.toFinset ⊆ S) = part M c ∪ part N c := by
      rw [← Finset.filter_union]
      have heq : H.edgeFinset = M ∪ N := by ext; simp [hH]
      rw [heq]
      exact Finset.filter_congr fun e he => inside he
    -- Connectivity gives |V(c)| ≤ |E(c)| + 1, while the N-edges use two vertices each.
    have hcard := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    have heq : (part M c ∪ part N c).card = Nat.card c.toSimpleGraph.edgeSet := by
      rw [← hpart]
      calc
        _ = (H.induce (S : Set V)).edgeFinset.card :=
          card_filter_edgeFinset_toFinset_subset (G := H) S
        _ = Nat.card (H.induce (S : Set V)).edgeSet :=
          edgeFinset_card.trans Nat.card_eq_fintype_card.symm
        _ = Nat.card c.toSimpleGraph.edgeSet :=
          congrArg (fun T : Set V => Nat.card (H.induce T).edgeSet) (Set.coe_toFinset _)
    rw [← heq] at hcard
    have hs : S.card = Nat.card c := by
      simp [S, ← Nat.card_eq_fintype_card]
    have := Finset.card_union_le (part M c) (part N c)
    omega
  obtain ⟨c, hc, hsmall⟩ := exists_small_component _ _ (sum_part M) (sum_part N) hlt surplus
  have hsub : part M c ∪ part N c ⊆ M ∪ N :=
    Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  obtain ⟨u, v, p, hp, hlen⟩ := augment_in_component G M (part M c) (part N c)
    (fun e he => hG e (hsub he))
    (fun a ha b hb => hM a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
    (fun a ha b hb => hN a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
    (Finset.filter_subset _ _) (by
      intro e he f hf x hxe hxf
      have hf' : comp f = c := (Finset.mem_union.mp hf).elim
        (fun h => (Finset.mem_filter.mp h).2) (fun h => (Finset.mem_filter.mp h).2)
      exact Finset.mem_filter.mpr ⟨he, (endpoint (Finset.mem_union_left N he) hxe).symm.trans
        ((endpoint (hsub hf) hxf).trans hf')⟩) hc
  have := surplus c
  exact ⟨u, v, p, hp, by omega⟩

end MetaMathlibExt
