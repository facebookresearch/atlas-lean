/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted

/-!
# Petersen's theorem
-/

private lemma walk_crossing
    {V : Type*} (G : SimpleGraph V)
    (S : Set V) {a b : V} (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ e ∈ p.edges, ∃ x ∈ S, ∃ y, y ∉ S ∧ e = s(x, y) := by
  revert ha
  induction p with
  | nil => intro ha; exact absurd ha hb
  | cons hadj tail ih =>
    rename_i u v w
    intro ha
    rw [SimpleGraph.Walk.edges_cons]
    by_cases hmem : v ∈ S
    · obtain ⟨_, he, x, hx, y, hy, rfl⟩ := ih hb hmem
      exact ⟨s(x, y), List.mem_cons_of_mem _ he, x, hx, y, hy, rfl⟩
    · exact ⟨s(u, v), List.mem_cons_self, u, ha, v, hmem, rfl⟩

private lemma mem_image_supp_not_mem
    {V : Type*} (G : SimpleGraph V)
    (u : Set V) (c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents)
    {x : V} (hx : x ∈ Subtype.val '' c.val.supp) : x ∉ u := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hzsub : z.val ∈ (⊤ : G.Subgraph).verts \ u := z.property
  rw [SimpleGraph.Subgraph.verts_top] at hzsub
  exact ((Set.mem_sdiff _).mp hzsub).2

private lemma neighbor_of_mem_image_supp
    {V : Type*} (G : SimpleGraph V)
    (u : Set V) (c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents)
    {x y : V} (hx : x ∈ Subtype.val '' c.val.supp)
    (hadj : G.Adj x y) (hy : y ∉ u) :
    y ∈ Subtype.val '' c.val.supp := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hxnu : z.val ∉ u := mem_image_supp_not_mem G u c ⟨z, hz, rfl⟩
  have hzV : z.val ∈ (⊤ : G.Subgraph).verts := by
    rw [SimpleGraph.Subgraph.verts_top]
    exact Set.mem_univ _
  have hyV : y ∈ (⊤ : G.Subgraph).verts := by
    rw [SimpleGraph.Subgraph.verts_top]
    exact Set.mem_univ _
  have hyverts : y ∈ ((⊤ : G.Subgraph).deleteVerts u).verts :=
    ((Set.mem_sdiff _).mpr ⟨hyV, hy⟩)
  have hxverts : z.val ∈ ((⊤ : G.Subgraph).deleteVerts u).verts :=
    ((Set.mem_sdiff _).mpr ⟨hzV, hxnu⟩)
  have hHadj : ((⊤ : G.Subgraph).deleteVerts u).Adj z.val y := by
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    refine ⟨hzV, hxnu, hyV, hy, ?_⟩
    rw [SimpleGraph.Subgraph.top_adj]
    exact hadj
  have hcoe : ((⊤ : G.Subgraph).deleteVerts u).coe.Adj z ⟨y, hyverts⟩ := hHadj
  have hmem := (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c.val hcoe).mp hz
  exact ⟨⟨y, hyverts⟩, hmem, rfl⟩

private lemma boundary_odd
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3)
    (u : Set V) (c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents)
    (E : Finset (Sym2 V))
    (hE : ∀ e, e ∈ E ↔ e ∈ G.edgeFinset ∧
      ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u, e = s(x, y)) :
    Odd E.card := by
  classical
  set S : Set V := Subtype.val '' c.val.supp with hSdef
  set T : Finset V := S.toFinset with hTdef
  have hSodd : Odd S.ncard := by
    rw [hSdef, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact c.prop
  have hTS : ∀ x : V, x ∈ T ↔ x ∈ S := fun x => Set.mem_toFinset
  have hdich : ∀ x ∈ S, ∀ y : V, G.Adj x y → y ∈ S ∨ y ∈ u := by
    intro x hx y hadj
    by_cases hy : y ∈ u
    · exact Or.inr hy
    · exact Or.inl (neighbor_of_mem_image_supp G u c hx hadj hy)
  have hSu : ∀ x ∈ S, x ∉ u := fun x hx => mem_image_supp_not_mem G u c hx
  have hdeg : ∀ x ∈ T, G.degree x =
      ((G.neighborFinset x).filter (· ∈ S)).card +
      ((G.neighborFinset x).filter (· ∈ u)).card := by
    intro x hx
    have hxS : x ∈ S := (hTS x).mp hx
    have hpart : (G.neighborFinset x).filter (· ∈ S) ∪
        (G.neighborFinset x).filter (· ∈ u) = G.neighborFinset x := by
      ext y
      simp only [Finset.mem_union, Finset.mem_filter, G.mem_neighborFinset x y]
      constructor
      · rintro (⟨hadj, -⟩ | ⟨hadj, -⟩) <;> exact hadj
      · intro hadj
        rcases hdich x hxS y hadj with h | h
        · exact Or.inl ⟨hadj, h⟩
        · exact Or.inr ⟨hadj, h⟩
    have hdisj : Disjoint ((G.neighborFinset x).filter (· ∈ S))
        ((G.neighborFinset x).filter (· ∈ u)) := by
      rw [Finset.disjoint_filter]
      intro y _ hS hyu
      exact hSu y hS hyu
    conv_lhs => rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hpart,
      Finset.card_union_of_disjoint hdisj]
  set DI : Finset (V × V) := (T ×ˢ T).filter (fun p => G.Adj p.1 p.2) with hDIdef
  set DB : Finset (V × V) := (T ×ˢ u.toFinset).filter (fun p => G.Adj p.1 p.2) with hDBdef
  set II : Finset (Sym2 V) :=
    G.edgeFinset.filter (fun e => ∃ x ∈ S, ∃ y ∈ S, e = s(x, y)) with hIIdef
  have hfibI : ∀ x ∈ T, (T.filter (fun y => G.Adj x y)).card
      = ((G.neighborFinset x).filter (· ∈ S)).card := by
    intro x _
    congr 1
    ext y
    simp only [Finset.mem_filter, hTS y, G.mem_neighborFinset x y, and_comm]
  have hsumI : (∑ x ∈ T, ((G.neighborFinset x).filter (· ∈ S)).card) = DI.card := by
    rw [hDIdef, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun x hx => by
      rw [← Finset.card_filter]
      exact (hfibI x hx).symm)
  have hfibB : ∀ x ∈ T, (u.toFinset.filter (fun y => G.Adj x y)).card
      = ((G.neighborFinset x).filter (· ∈ u)).card := by
    intro x _
    congr 1
    ext y
    simp only [Finset.mem_filter, Set.mem_toFinset, G.mem_neighborFinset x y,
      and_comm]
  have hsumB : (∑ x ∈ T, ((G.neighborFinset x).filter (· ∈ u)).card) = DB.card := by
    rw [hDBdef, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun x hx => by
      rw [← Finset.card_filter]
      exact (hfibB x hx).symm)
  have hmaps : Set.MapsTo (fun p : V × V => s(p.1, p.2)) (↑DI : Set (V × V)) ↑II := by
    intro p hp
    simp only [hDIdef, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      hTdef, Set.mem_toFinset] at hp
    obtain ⟨⟨hp1, hp2⟩, hadj⟩ := hp
    rw [hIIdef, Finset.mem_coe, Finset.mem_filter]
    refine ⟨(SimpleGraph.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr hadj),
      p.1, hp1, p.2, hp2, rfl⟩
  have hfib2 : ∀ e ∈ II,
      ({a ∈ DI | s(a.1, a.2) = e}).card = 2 := by
    intro e he
    rw [hIIdef, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    -- avoid `.mp` on the iff-name: decompose manually
    have heE : e ∈ G.edgeSet := he.1
    obtain ⟨a, haS, b, hbS, heq⟩ := he.2
    have hadj : G.Adj a b := by
      apply (G.mem_edgeSet).mp
      rw [← heq]
      exact heE
    have hane : a ≠ b := G.ne_of_adj hadj
    have hTf : ∀ z ∈ S, z ∈ T := fun z hz => (hTS z).mpr hz
    have hset : ({a ∈ DI | s(a.1, a.2) = e}) = {⟨a, b⟩, ⟨b, a⟩} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, hDIdef, Finset.mem_filter, Finset.mem_product,
        hTdef, Set.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq]
      rw [heq]
      constructor
      · rintro ⟨⟨⟨hxS, hyS⟩, hadjxy⟩, hseq⟩
        rw [Sym2.eq_iff] at hseq
        rcases hseq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact Or.inl ⟨rfl, rfl⟩
        · rw [h1, h2]; exact Or.inr ⟨rfl, rfl⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rw [h1, h2]; exact ⟨⟨⟨haS, hbS⟩, hadj⟩, rfl⟩
        · rw [h1, h2]
          refine ⟨⟨⟨hbS, haS⟩, hadj.symm⟩, ?_⟩
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
    rw [hset, Finset.card_pair]
    intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hane hcon.1
  have hDI2 : DI.card = 2 * II.card := by
    calc DI.card = ∑ b ∈ II, ({a ∈ DI | s(a.1, a.2) = b}).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ _b ∈ II, 2 := Finset.sum_congr rfl (fun e he => hfib2 e he)
      _ = 2 * II.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
  have himg : DB.image (fun p : V × V => s(p.1, p.2)) = E := by
    ext e
    simp only [Finset.mem_image]
    rw [hE e]
    constructor
    · rintro ⟨⟨x, y⟩, hmem, rfl⟩
      simp only [hDBdef, Finset.mem_filter, Finset.mem_product, hTdef,
        Set.mem_toFinset] at hmem
      obtain ⟨⟨hxS, hyu⟩, hadj⟩ := hmem
      refine ⟨(SimpleGraph.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr hadj),
        x, hxS, y, hyu, rfl⟩
    · rintro ⟨heF, x, hxS, y, hyu, heq⟩
      have hadj : G.Adj x y := by
        apply (G.mem_edgeSet).mp
        rw [← heq]
        exact (SimpleGraph.mem_edgeFinset).mp heF
      refine ⟨⟨x, y⟩, ?_, heq.symm⟩
      simp only [hDBdef, Finset.mem_filter, Finset.mem_product, hTdef,
        Set.mem_toFinset]
      exact ⟨⟨hxS, hyu⟩, hadj⟩
  have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) ↑DB := by
    intro p hp q hq h
    simp only [hDBdef, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      hTdef, Set.mem_toFinset] at hp hq
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have hpS : p.1 ∈ S := hp.1.1
      rw [h1] at hpS
      exact hSu q.2 hpS hq.1.2
  have hDBE : DB.card = E.card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  have hsum : (∑ x ∈ T, G.degree x) = DI.card + DB.card := by
    rw [Finset.sum_congr rfl (fun x hx => hdeg x hx)]
    rw [Finset.sum_add_distrib, hsumI, hsumB]
  have h3 : (∑ x ∈ T, G.degree x) = 3 * T.card := by
    rw [Finset.sum_congr rfl (fun x _ => hreg.degree_eq x)]
    simp [Finset.sum_const, smul_eq_mul, mul_comm]
  have hEq : 3 * T.card = 2 * II.card + E.card := by omega
  have hTeq : T.card = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
  have hTodd : Odd T.card := by
    rw [hTeq]
    exact hSodd
  obtain ⟨m, hm⟩ : Odd (3 * T.card) := Odd.mul ⟨1, rfl⟩ hTodd
  obtain ⟨k, hk⟩ : Even (2 * II.card) := ⟨II.card, two_mul _⟩
  have hmk : k ≤ m := by omega
  exact ⟨m - k, by omega⟩

private lemma boundary_not_one
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbridge : ∀ e ∈ G.edgeSet, ¬G.IsBridge e)
    (u : Set V) (c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents)
    (E : Finset (Sym2 V))
    (hE : ∀ e, e ∈ E ↔ e ∈ G.edgeFinset ∧
      ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u, e = s(x, y)) :
    E.card ≠ 1 := by
  classical
  set S : Set V := Subtype.val '' c.val.supp with hSdef
  intro h1
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
  have heE : e ∈ E := by
    rw [he]
    exact Finset.mem_singleton_self e
  obtain ⟨heF, x, hxS, y, hyu, heq⟩ := (hE e).mp heE
  have hedge : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).mp heF
  have hSu : ∀ x ∈ S, x ∉ u := fun x hx => mem_image_supp_not_mem G u c hx
  have hyS : y ∉ S := fun h => hSu y h hyu
  have hbr : G.IsBridge e := by
    rw [heq, SimpleGraph.isBridge_iff_forall_walk_mem_edges]
    intro p
    obtain ⟨e', he'p, x', hx'S, y', hy'S, heq'⟩ := walk_crossing G S p hxS hyS
    have hedge' : e' ∈ G.edgeSet := p.edges_subset_edgeSet he'p
    have hadj' : G.Adj x' y' := by
      apply (G.mem_edgeSet).mp
      rw [← heq']
      exact hedge'
    have hy'u : y' ∈ u := by
      by_cases h : y' ∈ u
      · exact h
      · exfalso
        exact hy'S (neighbor_of_mem_image_supp G u c hx'S hadj' h)
    have he'E : e' ∈ E := (hE e').mpr
      ⟨(SimpleGraph.mem_edgeFinset).mpr hedge', x', hx'S, y', hy'u, heq'⟩
    have h1e : e' = e := Finset.mem_singleton.mp (by rw [← he]; exact he'E)
    have hfin : e' = s(x, y) := h1e.trans heq
    rw [hfin] at he'p
    exact he'p
  exact (hbridge e hedge) hbr

private lemma boundary_disjoint
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : Set V)
    (c1 c2 : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents)
    (hne : c1.val ≠ c2.val)
    (E1 E2 : Finset (Sym2 V))
    (hE1 : ∀ e, e ∈ E1 ↔ e ∈ G.edgeFinset ∧
      ∃ x ∈ Subtype.val '' c1.val.supp, ∃ y ∈ u, e = s(x, y))
    (hE2 : ∀ e, e ∈ E2 ↔ e ∈ G.edgeFinset ∧
      ∃ x ∈ Subtype.val '' c2.val.supp, ∃ y ∈ u, e = s(x, y)) :
    Disjoint E1 E2 := by
  classical
  have hsupp : Disjoint c1.val.supp c2.val.supp :=
    SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hne
  have hS : Disjoint (Subtype.val '' c1.val.supp) (Subtype.val '' c2.val.supp) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨z1, hz1, rfl⟩ := hx1
    obtain ⟨z2, hz2, hval⟩ := hx2
    have h12 : z1 = z2 := Subtype.val_injective hval.symm
    have hz2' : z1 ∈ c2.val.supp := by
      rw [h12]
      exact hz2
    exact (Set.disjoint_left.mp hsupp hz1) hz2'
  rw [Finset.disjoint_left]
  intro e he1 he2
  obtain ⟨-, x1, hx1, y1, -, heq1⟩ := (hE1 e).mp he1
  obtain ⟨-, x2, hx2, y2, hy2u, heq2⟩ := (hE2 e).mp he2
  have hsym : s(x1, y1) = s(x2, y2) := heq1.symm.trans heq2
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx2' : x1 ∈ Subtype.val '' c2.val.supp := by
      rw [h1]
      exact hx2
    exact (Set.disjoint_left.mp hS hx1) hx2'
  · have hy2S1 : y2 ∈ Subtype.val '' c1.val.supp := by
      rw [← h1]
      exact hx1
    exact (mem_image_supp_not_mem G u c1 hy2S1) hy2u

/-- **Petersen's theorem on cubic graphs.** Every finite simple graph that is $3$-regular
and has no bridge, that is, no edge whose removal disconnects its endpoints, has a perfect
matching: a set of edges of the graph such that every vertex lies on exactly one of them. -/
theorem petersen_bridgeless_cubic_has_perfect_matching_general
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3)
    (hbridge : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  rw [SimpleGraph.tutte]
  intro u hviol
  have hlt : u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard :=
    hviol
  have key : ∀ c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents, 3 ≤
      (G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u,
        e = s(x, y))).card := by
    intro c
    set E := G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp,
      ∃ y ∈ u, e = s(x, y)) with hEdef
    have hEchar : ∀ e, e ∈ E ↔ e ∈ G.edgeFinset ∧
        ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u, e = s(x, y) := by
      intro e
      simp only [hEdef, Finset.mem_filter]
    have hodd := boundary_odd G hreg u c E hEchar
    have hne := boundary_not_one G hbridge u c E hEchar
    obtain ⟨m, hm⟩ := hodd
    omega
  set O : Finset ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents :=
    Finset.univ with hOdef
  have hOcard : O.card =
      ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard := by
    rw [hOdef, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have h1 : ∑ _c ∈ O, 3 ≤ ∑ c ∈ O,
      (G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u,
        e = s(x, y))).card :=
    Finset.sum_le_sum (fun c _ => key c)
  rw [Finset.sum_const, smul_eq_mul, mul_comm] at h1
  have hdisj : Set.PairwiseDisjoint (↑O)
      (fun c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents =>
      G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u,
        e = s(x, y))) := by
    intro c1 hc1 c2 hc2 hne12
    have hneV : c1.val ≠ c2.val := fun h => hne12 (Subtype.ext h)
    exact boundary_disjoint G u c1 c2 hneV _ _
      (fun e => Finset.mem_filter) (fun e => Finset.mem_filter)
  have hcardU : (O.biUnion (fun c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents =>
      G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u,
        e = s(x, y)))).card
      = ∑ c ∈ O, (G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp,
        ∃ y ∈ u, e = s(x, y))).card :=
    Finset.card_biUnion hdisj
  set F : Finset (Sym2 V) :=
    G.edgeFinset.filter (fun e => ∃ y ∈ u, y ∈ e) with hFdef
  have hsub : O.biUnion (fun c : ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents =>
      G.edgeFinset.filter (fun e => ∃ x ∈ Subtype.val '' c.val.supp, ∃ y ∈ u,
        e = s(x, y))) ⊆ F := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨c, -, hec⟩ := he
    simp only [Finset.mem_filter] at hec
    obtain ⟨heF, x, -, y, hyu, heq⟩ := hec
    simp only [hFdef, Finset.mem_filter]
    refine ⟨heF, y, hyu, ?_⟩
    rw [heq]
    exact (Sym2.mem_iff).mpr (Or.inr rfl)
  have hFcard : F.card ≤ 3 * u.ncard := by
    have hsub2 : F ⊆ u.toFinset.biUnion (fun y => G.incidenceFinset y) := by
      intro e he
      simp only [hFdef, Finset.mem_filter] at he
      obtain ⟨heF, y, hyu, hye⟩ := he
      rw [Finset.mem_biUnion]
      refine ⟨y, Set.mem_toFinset.mpr hyu, ?_⟩
      rw [G.mem_incidenceFinset]
      exact ⟨(SimpleGraph.mem_edgeFinset).mp heF, hye⟩
    have hle := Finset.card_le_card hsub2
    have hle2 := Finset.card_biUnion_le (s := u.toFinset)
      (t := fun y => G.incidenceFinset y)
    have hle := hle.trans hle2
    have h3 : ∀ y ∈ u.toFinset, (G.incidenceFinset y).card = 3 := by
      intro y _
      rw [G.card_incidenceFinset_eq_degree, hreg.degree_eq]
    rw [Finset.sum_congr rfl h3] at hle
    rw [Finset.sum_const, smul_eq_mul, mul_comm] at hle
    rw [← Set.ncard_eq_toFinset_card'] at hle
    exact hle
  rw [← hcardU] at h1
  have hfin : 3 * O.card ≤ F.card := h1.trans (Finset.card_le_card hsub)
  rw [hOcard] at hfin
  omega

set_option linter.unusedDecidableInType false in
/--
**Petersen's perfect matching theorem.** Every finite simple graph that is $3$-regular and
has no bridge, that is, no edge whose removal disconnects its endpoints, has a perfect
matching: a set of edges of the graph such that every vertex lies on exactly one of them.

Proves `Wanted` entry `petersen_bridgeless_cubic_has_perfect_matching`.

Source: J. Petersen, "Die Theorie der regulären graphs", Acta Mathematica 15 (1891), 193-220, DOI
10.1007/BF02392606.
It follows from `petersen_bridgeless_cubic_has_perfect_matching_general`; the instance
`[DecidableEq V]` is unused and keeps the source's shape.
-/
theorem petersen_bridgeless_cubic_has_perfect_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3)
    (hbridge : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  exact petersen_bridgeless_cubic_has_perfect_matching_general G hreg hbridge

end MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted
