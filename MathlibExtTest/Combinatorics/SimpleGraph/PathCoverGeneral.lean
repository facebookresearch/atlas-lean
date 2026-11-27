/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `bd2b030c7d44` (PR #6022).
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.PathCoverGeneral
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.PathCoverGeneral

open MathlibExt.Combinatorics.Digraph.PathCoverWanted
open MathlibExt.Combinatorics.SimpleGraph.PathCoverGeneralWanted
open MathlibExt.Combinatorics.Matching (IsMaximumMatching exists_maximum_matching)

/-- Every edge of a double-cover subgraph is a cross edge over an arc:
same-side pairs cannot occur since the double cover has no same-side edges. -/
private theorem edge_eq_cross_of_mem {W : Type*} {D : Digraph W}
    (M' : (doubleCover D).Subgraph) {e : Sym2 (W ⊕ W)}
    (he : e ∈ M'.edgeSet) :
    ∃ u v, D.Adj u v ∧ e = s(Sum.inl u, Sum.inr v) := by
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      exact absurd (M'.adj_sub he) (doubleCover_not_adj_inl_inl D u v)
    | inr v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      exact ⟨u, v, M'.adj_sub he, rfl⟩
  | inr u =>
    cases b with
    | inl v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      exact ⟨v, u, M'.adj_sub he, Sym2.eq_swap⟩
    | inr v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      exact absurd (M'.adj_sub he) (doubleCover_not_adj_inr_inr D u v)

/-- In a matching subgraph, at most one edge passes through a given vertex:
two such edges would give the vertex two distinct neighbors. -/
private theorem ncard_edges_at_vertex_le_one {W : Type*} [Finite W]
    {G : SimpleGraph W} (M' : G.Subgraph) (hM' : M'.IsMatching) (x : W) :
    {e ∈ M'.edgeSet | x ∈ e}.ncard ≤ 1 := by
  have : Finite (Sym2 W) := Quot.finite _
  rw [Set.ncard_le_one (Set.toFinite _)]
  intro e₁ h₁ e₂ h₂
  obtain ⟨hm₁, hx₁⟩ := h₁
  obtain ⟨hm₂, hx₂⟩ := h₂
  have edge_form : ∀ e : Sym2 W, e ∈ M'.edgeSet → x ∈ e →
      ∃ y, M'.Adj x y ∧ e = s(x, y) := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he hx
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨b, he, rfl⟩
    · exact ⟨a, M'.adj_symm he, Sym2.eq_swap⟩
  obtain ⟨y₁, hy₁, rfl⟩ := edge_form e₁ hm₁ hx₁
  obtain ⟨y₂, hy₂, rfl⟩ := edge_form e₂ hm₂ hx₂
  have hy : y₁ = y₂ := hM'.eq_of_adj_left hy₁ hy₂
  subst hy
  rfl

/-- The two-sources/middle/two-sinks DAG from the module documentation:
sources `0, 1` feed the middle vertex `2`, which feeds sinks `3, 4`. A
reducible abbrev so `decide` can evaluate adjacency. Genuinely non-transitive:
`0 → 2 → 3` with no `0 → 3` arc. -/
private abbrev bowtie : Digraph (Fin 5) :=
  ⟨fun x y => (x.val = 0 ∨ x.val = 1) ∧ y.val = 2 ∨
    x.val = 2 ∧ (y.val = 3 ∨ y.val = 4)⟩

/-- The bowtie is not transitive: `0 → 2 → 3` but no `0 → 3` arc. -/
private theorem bowtie_not_transitive : ¬ IsTransitiveDAG bowtie := by
  intro h
  exact absurd (h.trans 0 2 3 (by decide) (by decide)) (by decide)

/-- Adjacency in the bowtie strictly increases the vertex number. -/
private theorem bowtie_adj_lt (x y : Fin 5) :
    bowtie.Adj x y → x.val < y.val := by
  revert x y
  decide

/-- Reachability in the bowtie strictly increases the vertex number. -/
private theorem bowtie_transGen_lt (a b : Fin 5) :
    Relation.TransGen bowtie.Adj a b → a.val < b.val := by
  intro hab
  induction hab with
  | single h => exact bowtie_adj_lt _ _ h
  | tail _ hbc ih => exact lt_trans ih (bowtie_adj_lt _ _ hbc)

/-- The bowtie is a DAG: a reachability cycle would strictly decrease the
vertex number around the cycle. -/
private theorem bowtie_dag : bowtie.IsAcyclic := by
  intro x h
  exact lt_irrefl _ (bowtie_transGen_lt x x h)

/-- The four arcs of the bowtie, characterized. -/
private theorem bowtie_adj_iff (a b : Fin 5) :
    bowtie.Adj a b ↔
      (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 2 ∧ b = 3) ∨ (a = 2 ∧ b = 4) := by
  revert a b
  decide

/-- Nothing points at source `0`. -/
private theorem bowtie_no_adj_to_zero (c : Fin 5) : ¬ bowtie.Adj c 0 := by
  revert c
  decide

/-- Nothing points at source `1`. -/
private theorem bowtie_no_adj_to_one (c : Fin 5) : ¬ bowtie.Adj c 1 := by
  revert c
  decide

/-- Nothing reaches source `0`: every reachability witness would end in an
arc into `0`. -/
private theorem bowtie_no_transGen_to_zero (a : Fin 5) :
    ¬ Relation.TransGen bowtie.Adj a 0 := by
  intro h
  cases h with
  | single h => exact absurd h (bowtie_no_adj_to_zero _)
  | tail _ hbc => exact absurd hbc (bowtie_no_adj_to_zero _)

/-- Nothing reaches source `1`: every reachability witness would end in an
arc into `1`. -/
private theorem bowtie_no_transGen_to_one (a : Fin 5) :
    ¬ Relation.TransGen bowtie.Adj a 1 := by
  intro h
  cases h with
  | single h => exact absurd h (bowtie_no_adj_to_one _)
  | tail _ hbc => exact absurd hbc (bowtie_no_adj_to_one _)

/-- The double cover of the bowtie is bipartite. -/
example : (doubleCover bowtie).IsBipartite :=
  doubleCover_bipartite bowtie

/-- An explicit 2-edge matching subgraph of the bowtie double cover, over the
arcs `(0, 2)` and `(2, 3)`. A reducible abbrev so `decide` can evaluate
adjacency and membership. -/
private abbrev bowtieMatching : (doubleCover bowtie).Subgraph where
  verts := {Sum.inl 0, Sum.inl 2, Sum.inr 2, Sum.inr 3}
  Adj := fun x y =>
    (x = Sum.inl 0 ∧ y = Sum.inr 2) ∨ (x = Sum.inr 2 ∧ y = Sum.inl 0) ∨
    (x = Sum.inl 2 ∧ y = Sum.inr 3) ∨ (x = Sum.inr 3 ∧ y = Sum.inl 2)
  adj_sub := by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      show bowtie.Adj _ _ <;> decide
  edge_vert := by
    intro x y h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  symm := ⟨by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide⟩

/-- The explicit subgraph is a matching: each endpoint sees exactly one
neighbor. -/
private theorem bowtieMatching_isMatching : bowtieMatching.IsMatching := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨Sum.inr 2, by decide, by decide⟩
  · exact ⟨Sum.inr 3, by decide, by decide⟩
  · exact ⟨Sum.inl 0, by decide, by decide⟩
  · exact ⟨Sum.inl 2, by decide, by decide⟩

/-- The first explicit edge lies in the subgraph. -/
private theorem bowtieMatching_mem_left :
    s(Sum.inl (0 : Fin 5), Sum.inr 2) ∈ bowtieMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The second explicit edge lies in the subgraph. -/
private theorem bowtieMatching_mem_right :
    s(Sum.inl (2 : Fin 5), Sum.inr 3) ∈ bowtieMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The two explicit edges are distinct. -/
private theorem bowtieMatching_edges_ne :
    s(Sum.inl (0 : Fin 5), Sum.inr (2 : Fin 5)) ≠
      s(Sum.inl (2 : Fin 5), Sum.inr (3 : Fin 5)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- Every matching subgraph of the bowtie double cover has at most 2 edges:
every arc touches vertex `2` on one side, so every edge passes through
`Sum.inl 2` or `Sum.inr 2`, each hosting at most one edge. -/
private theorem bowtie_subgraph_matching_ncard_le
    (M' : (doubleCover bowtie).Subgraph) (hM' : M'.IsMatching) :
    M'.edgeSet.ncard ≤ 2 := by
  have : Finite (Sym2 (Fin 5 ⊕ Fin 5)) := Quot.finite _
  have hcover : M'.edgeSet ⊆ {e ∈ M'.edgeSet | Sum.inl 2 ∈ e} ∪
      {e ∈ M'.edgeSet | Sum.inr 2 ∈ e} := by
    intro e he
    obtain ⟨u, v, hadj, rfl⟩ := edge_eq_cross_of_mem M' he
    rw [bowtie_adj_iff] at hadj
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
    · exact Or.inr ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
    · exact Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inl rfl⟩
    · exact Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inl rfl⟩
  have h1 := ncard_edges_at_vertex_le_one M' hM' (Sum.inl (2 : Fin 5))
  have h2 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (2 : Fin 5))
  have hle := Set.ncard_le_ncard hcover (Set.toFinite _)
  have hunion := Set.ncard_union_le {e ∈ M'.edgeSet | Sum.inl 2 ∈ e}
    {e ∈ M'.edgeSet | Sum.inr 2 ∈ e}
  omega

/-- The explicit matching has 2 edges: two distinct edges below, at most two
above. -/
private theorem bowtieMatching_ncard_eq :
    bowtieMatching.edgeSet.ncard = 2 := by
  have : Finite (Sym2 (Fin 5 ⊕ Fin 5)) := Quot.finite _
  have hsub : ({s(Sum.inl (0 : Fin 5), Sum.inr 2),
      s(Sum.inl 2, Sum.inr (3 : Fin 5))} : Set _) ⊆
      bowtieMatching.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact bowtieMatching_mem_left
    · exact bowtieMatching_mem_right
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair bowtieMatching_edges_ne] at hle
  have hub := bowtie_subgraph_matching_ncard_le _ bowtieMatching_isMatching
  omega

/-- The explicit 2-edge matching is maximum. -/
private theorem bowtieMatching_isMaximum :
    IsMaximumMatching (doubleCover bowtie) bowtieMatching :=
  ⟨bowtieMatching_isMatching, fun M' hM' => by
    rw [bowtieMatching_ncard_eq]
    exact bowtie_subgraph_matching_ncard_le M' hM'⟩

/-- The headline theorem through the standard API: the minimum path cover of
the (non-transitive) bowtie from its maximum matching subgraph. -/
example : minPathCoverSize bowtie = 3 := by
  have h := minPathCover_eq_card_sub_ncard_maximum bowtie bowtie_dag
    bowtieMatching_isMaximum
  rw [bowtieMatching_ncard_eq, Fintype.card_fin] at h
  exact h

/-- Any maximum matching subgraph gives the same answer. -/
example (M : (doubleCover bowtie).Subgraph)
    (hM : IsMaximumMatching (doubleCover bowtie) M) :
    minPathCoverSize bowtie = 3 := by
  have h := minPathCover_eq_card_sub_ncard_maximum bowtie bowtie_dag hM
  have hmax : M.edgeSet.ncard = 2 := by
    have hEq := hM.ncard_eq bowtieMatching_isMaximum
    rw [bowtieMatching_ncard_eq] at hEq
    exact hEq
  rw [hmax, Fintype.card_fin] at h
  exact h

/-- A maximum matching exists and attains the bound. -/
example : ∃ M : (doubleCover bowtie).Subgraph,
    IsMaximumMatching (doubleCover bowtie) M ∧ M.edgeSet.ncard = 2 := by
  obtain ⟨M, hM⟩ := exists_maximum_matching (doubleCover bowtie)
  refine ⟨M, hM, ?_⟩
  have hEq := hM.ncard_eq bowtieMatching_isMaximum
  rw [bowtieMatching_ncard_eq] at hEq
  exact hEq

/-- An explicit 3-path cover of the bowtie: `{0, 2, 3}`, `{1}`, `{4}`. -/
private theorem bowtie_cover : IsPathCover bowtie
    ({{0, 2, 3}, {1}, {4}} : Finset (Finset (Fin 5))) := by
  have h023 : IsPath bowtie ({0, 2, 3} : Finset (Fin 5)) := by
    refine ⟨[0, 2, 3], by decide, by decide, by decide, ?_⟩
    ext a
    simp
  have h1 : IsPath bowtie ({1} : Finset (Fin 5)) := by
    refine ⟨[1], by decide, by decide, by decide, ?_⟩
    ext a
    simp
  have h4 : IsPath bowtie ({4} : Finset (Fin 5)) := by
    refine ⟨[4], by decide, by decide, by decide, ?_⟩
    ext a
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨h023, ⟨0, by decide⟩⟩
    · exact ⟨h1, ⟨1, by decide⟩⟩
    · exact ⟨h4, ⟨4, by decide⟩⟩
  · intro s hs t ht hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · decide
    · exact absurd rfl hne
    · decide
    · decide
    · decide
    · exact absurd rfl hne
  · intro a
    fin_cases a
    · exact ⟨{0, 2, 3}, by simp, by decide⟩
    · exact ⟨{1}, by simp, by decide⟩
    · exact ⟨{0, 2, 3}, by simp, by decide⟩
    · exact ⟨{0, 2, 3}, by simp, by decide⟩
    · exact ⟨{4}, by simp, by decide⟩

/-- Three paths suffice for the bowtie, by the explicit cover. -/
example : minPathCoverSize bowtie ≤ 3 := by
  have h := minPathCoverSize_le_card bowtie bowtie_cover
  have hcard : (({{0, 2, 3}, {1}, {4}} : Finset (Finset (Fin 5)))).card = 3 := by
    decide
  omega

/-- Reachability from `0` to `2` in the bowtie. -/
private theorem bowtie_trans_0_2 : Relation.TransGen bowtie.Adj 0 2 :=
  Relation.TransGen.single (by decide)

/-- Reachability from `2` to `3` in the bowtie. -/
private theorem bowtie_trans_2_3 : Relation.TransGen bowtie.Adj 2 3 :=
  Relation.TransGen.single (by decide)

/-- Reachability from `1` to `4` in the bowtie, via the middle vertex. -/
private theorem bowtie_trans_1_4 : Relation.TransGen bowtie.Adj 1 4 :=
  Relation.TransGen.tail
    (Relation.TransGen.single (show bowtie.Adj 1 2 from by decide))
    (show bowtie.Adj 2 4 from by decide)

/-- An explicit 3-edge matching subgraph of the transitive-closure double
cover, over the reachability arcs `(0, 2)`, `(2, 3)`, `(1, 4)`. -/
private abbrev bowtieClosureMatching :
    (doubleCover (transClosure bowtie)).Subgraph where
  verts := {Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 2, Sum.inr 3, Sum.inr 4}
  Adj := fun x y =>
    (x = Sum.inl 0 ∧ y = Sum.inr 2) ∨ (x = Sum.inr 2 ∧ y = Sum.inl 0) ∨
    (x = Sum.inl 2 ∧ y = Sum.inr 3) ∨ (x = Sum.inr 3 ∧ y = Sum.inl 2) ∨
    (x = Sum.inl 1 ∧ y = Sum.inr 4) ∨ (x = Sum.inr 4 ∧ y = Sum.inl 1)
  adj_sub := by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Relation.TransGen bowtie.Adj 0 2
      exact bowtie_trans_0_2
    · show Relation.TransGen bowtie.Adj 0 2
      exact bowtie_trans_0_2
    · show Relation.TransGen bowtie.Adj 2 3
      exact bowtie_trans_2_3
    · show Relation.TransGen bowtie.Adj 2 3
      exact bowtie_trans_2_3
    · show Relation.TransGen bowtie.Adj 1 4
      exact bowtie_trans_1_4
    · show Relation.TransGen bowtie.Adj 1 4
      exact bowtie_trans_1_4
  edge_vert := by
    intro x y h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  symm := ⟨by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide⟩

/-- The explicit closure subgraph is a matching. -/
private theorem bowtieClosureMatching_isMatching :
    bowtieClosureMatching.IsMatching := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Sum.inr 2, by decide, by decide⟩
  · exact ⟨Sum.inr 4, by decide, by decide⟩
  · exact ⟨Sum.inr 3, by decide, by decide⟩
  · exact ⟨Sum.inl 0, by decide, by decide⟩
  · exact ⟨Sum.inl 2, by decide, by decide⟩
  · exact ⟨Sum.inl 1, by decide, by decide⟩

/-- The `(0, 2)` explicit closure edge lies in the subgraph. -/
private theorem bowtieClosureMatching_mem_02 :
    s(Sum.inl (0 : Fin 5), Sum.inr 2) ∈
      bowtieClosureMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The `(2, 3)` explicit closure edge lies in the subgraph. -/
private theorem bowtieClosureMatching_mem_23 :
    s(Sum.inl (2 : Fin 5), Sum.inr 3) ∈
      bowtieClosureMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The `(1, 4)` explicit closure edge lies in the subgraph. -/
private theorem bowtieClosureMatching_mem_14 :
    s(Sum.inl (1 : Fin 5), Sum.inr 4) ∈
      bowtieClosureMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The first two explicit closure edges are distinct. -/
private theorem bowtieClosureMatching_ne_02_23 :
    s(Sum.inl (0 : Fin 5), Sum.inr (2 : Fin 5)) ≠
      s(Sum.inl (2 : Fin 5), Sum.inr (3 : Fin 5)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- The first and third explicit closure edges are distinct. -/
private theorem bowtieClosureMatching_ne_02_14 :
    s(Sum.inl (0 : Fin 5), Sum.inr (2 : Fin 5)) ≠
      s(Sum.inl (1 : Fin 5), Sum.inr (4 : Fin 5)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- The last two explicit closure edges are distinct. -/
private theorem bowtieClosureMatching_ne_23_14 :
    s(Sum.inl (2 : Fin 5), Sum.inr (3 : Fin 5)) ≠
      s(Sum.inl (1 : Fin 5), Sum.inr (4 : Fin 5)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- Every matching subgraph of the transitive-closure double cover has at most
3 edges: nothing reaches the sources `0, 1`, so every edge passes through one
of `Sum.inr 2`, `Sum.inr 3`, `Sum.inr 4`, each hosting at most one edge. -/
private theorem bowtieClosure_subgraph_matching_ncard_le
    (M' : (doubleCover (transClosure bowtie)).Subgraph)
    (hM' : M'.IsMatching) : M'.edgeSet.ncard ≤ 3 := by
  have : Finite (Sym2 (Fin 5 ⊕ Fin 5)) := Quot.finite _
  have hcover : M'.edgeSet ⊆ {e ∈ M'.edgeSet | Sum.inr 2 ∈ e} ∪
      ({e ∈ M'.edgeSet | Sum.inr 3 ∈ e} ∪
        {e ∈ M'.edgeSet | Sum.inr 4 ∈ e}) := by
    intro e he
    obtain ⟨u, v, hadj, rfl⟩ := edge_eq_cross_of_mem M' he
    fin_cases v
    · exact (bowtie_no_transGen_to_zero u hadj).elim
    · exact (bowtie_no_transGen_to_one u hadj).elim
    · exact Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩)
    · exact Or.inr (Or.inr ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩)
  have h2 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (2 : Fin 5))
  have h3 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (3 : Fin 5))
  have h4 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (4 : Fin 5))
  have hle := Set.ncard_le_ncard hcover (Set.toFinite _)
  have hunion := Set.ncard_union_le {e ∈ M'.edgeSet | Sum.inr 2 ∈ e}
    ({e ∈ M'.edgeSet | Sum.inr 3 ∈ e} ∪ {e ∈ M'.edgeSet | Sum.inr 4 ∈ e})
  have hunion2 := Set.ncard_union_le {e ∈ M'.edgeSet | Sum.inr 3 ∈ e}
    {e ∈ M'.edgeSet | Sum.inr 4 ∈ e}
  omega

/-- The explicit closure matching has 3 edges. -/
private theorem bowtieClosureMatching_ncard_eq :
    bowtieClosureMatching.edgeSet.ncard = 3 := by
  have : Finite (Sym2 (Fin 5 ⊕ Fin 5)) := Quot.finite _
  have hsub : ({s(Sum.inl (0 : Fin 5), Sum.inr 2),
      s(Sum.inl 2, Sum.inr (3 : Fin 5)),
      s(Sum.inl 1, Sum.inr (4 : Fin 5))} : Set _) ⊆
      bowtieClosureMatching.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact bowtieClosureMatching_mem_02
    · exact bowtieClosureMatching_mem_23
    · exact bowtieClosureMatching_mem_14
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : ({s(Sum.inl (0 : Fin 5), Sum.inr (2 : Fin 5)),
      s(Sum.inl 2, Sum.inr (3 : Fin 5)),
      s(Sum.inl 1, Sum.inr (4 : Fin 5))} : Set _).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      intro hcon
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
      rcases hcon with hcon | hcon
      · exact absurd hcon bowtieClosureMatching_ne_02_23
      · exact absurd hcon bowtieClosureMatching_ne_02_14)]
    rw [Set.ncard_pair bowtieClosureMatching_ne_23_14]
  rw [hcard] at hle
  have hub := bowtieClosure_subgraph_matching_ncard_le _
    bowtieClosureMatching_isMatching
  omega

/-- The explicit 3-edge closure matching is maximum. -/
private theorem bowtieClosureMatching_isMaximum :
    IsMaximumMatching (doubleCover (transClosure bowtie))
      bowtieClosureMatching :=
  ⟨bowtieClosureMatching_isMatching, fun M' hM' => by
    rw [bowtieClosureMatching_ncard_eq]
    exact bowtieClosure_subgraph_matching_ncard_le M' hM'⟩

/-- The reachability width of the bowtie is 2 (`5 - 3`), strictly below its
minimum path cover 3: the Dilworth/Kőnig answer governs the transitive
closure, not the DAG itself. -/
example : maxAntichainSize (transClosure bowtie)
    (isTransitiveDAG_transClosure bowtie bowtie_dag) = 2 := by
  have h := width_eq_card_sub_ncard_maximum_transClosure bowtie bowtie_dag
    bowtieClosureMatching_isMaximum
  rw [bowtieClosureMatching_ncard_eq, Fintype.card_fin] at h
  exact h

/-- Any maximum matching subgraph of the closure double cover gives the same
width. -/
example (M : (doubleCover (transClosure bowtie)).Subgraph)
    (hM : IsMaximumMatching (doubleCover (transClosure bowtie)) M) :
    maxAntichainSize (transClosure bowtie)
      (isTransitiveDAG_transClosure bowtie bowtie_dag) = 2 := by
  have h := width_eq_card_sub_ncard_maximum_transClosure bowtie bowtie_dag hM
  have hmax : M.edgeSet.ncard = 3 := by
    have hEq := hM.ncard_eq bowtieClosureMatching_isMaximum
    rw [bowtieClosureMatching_ncard_eq] at hEq
    exact hEq
  rw [hmax, Fintype.card_fin] at h
  exact h

/-- The width/path-cover distinction on the bowtie: 3 paths, width 2. -/
example : minPathCoverSize bowtie = 3 ∧
    maxAntichainSize (transClosure bowtie)
      (isTransitiveDAG_transClosure bowtie bowtie_dag) = 2 := by
  have hcover := minPathCover_eq_card_sub_ncard_maximum bowtie bowtie_dag
    bowtieMatching_isMaximum
  rw [bowtieMatching_ncard_eq, Fintype.card_fin] at hcover
  have hwidth := width_eq_card_sub_ncard_maximum_transClosure bowtie bowtie_dag
    bowtieClosureMatching_isMaximum
  rw [bowtieClosureMatching_ncard_eq, Fintype.card_fin] at hwidth
  exact ⟨hcover, hwidth⟩

/-- The 2-arc chain on three vertices: arcs `0 → 1` and `1 → 2` but no
`0 → 2`. Non-transitive, yet the minimum path-cover values coincide before
and after transitive closure (both are one path), showing transitivity is
sufficient but not necessary for coincidence. -/
private abbrev chain3 : Digraph (Fin 3) :=
  ⟨fun x y => x.val = 0 ∧ y.val = 1 ∨ x.val = 1 ∧ y.val = 2⟩

/-- The chain is not transitive: `0 → 1 → 2` but no `0 → 2` arc. -/
private theorem chain3_not_transitive : ¬ IsTransitiveDAG chain3 := by
  intro h
  exact absurd (h.trans 0 1 2 (by decide) (by decide)) (by decide)

/-- Adjacency in the chain strictly increases the vertex number. -/
private theorem chain3_adj_lt (x y : Fin 3) :
    chain3.Adj x y → x.val < y.val := by
  revert x y
  decide

/-- The chain is a DAG. -/
private theorem chain3_dag : chain3.IsAcyclic := by
  intro x h
  have hlt : ∀ a b : Fin 3,
      Relation.TransGen chain3.Adj a b → a.val < b.val := by
    intro a b hab
    induction hab with
    | single h => exact chain3_adj_lt _ _ h
    | tail _ hbc ih => exact lt_trans ih (chain3_adj_lt _ _ hbc)
  exact lt_irrefl _ (hlt x x h)

/-- The two arcs of the chain, characterized. -/
private theorem chain3_adj_iff (a b : Fin 3) :
    chain3.Adj a b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by
  revert a b
  decide

/-- Nothing reaches `0` in the chain. -/
private theorem chain3_no_transGen_to_zero (a : Fin 3) :
    ¬ Relation.TransGen chain3.Adj a 0 := by
  have hno : ∀ c : Fin 3, ¬ chain3.Adj c 0 := by
    intro c
    revert c
    decide
  intro h
  cases h with
  | single h => exact absurd h (hno _)
  | tail _ hbc => exact absurd hbc (hno _)

/-- Reachability from `0` to `2` in the chain, via the middle vertex. -/
private theorem chain3_trans_0_2 : Relation.TransGen chain3.Adj 0 2 :=
  Relation.TransGen.tail
    (Relation.TransGen.single (show chain3.Adj 0 1 from by decide))
    (show chain3.Adj 1 2 from by decide)

/-- An explicit 2-edge matching subgraph of the chain double cover, over the
arcs `(0, 1)` and `(1, 2)`. -/
private abbrev chain3Matching : (doubleCover chain3).Subgraph where
  verts := {Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 2}
  Adj := fun x y =>
    (x = Sum.inl 0 ∧ y = Sum.inr 1) ∨ (x = Sum.inr 1 ∧ y = Sum.inl 0) ∨
    (x = Sum.inl 1 ∧ y = Sum.inr 2) ∨ (x = Sum.inr 2 ∧ y = Sum.inl 1)
  adj_sub := by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      show chain3.Adj _ _ <;> decide
  edge_vert := by
    intro x y h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  symm := ⟨by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide⟩

/-- The explicit chain subgraph is a matching. -/
private theorem chain3Matching_isMatching : chain3Matching.IsMatching := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨Sum.inr 1, by decide, by decide⟩
  · exact ⟨Sum.inr 2, by decide, by decide⟩
  · exact ⟨Sum.inl 0, by decide, by decide⟩
  · exact ⟨Sum.inl 1, by decide, by decide⟩

/-- The first explicit chain edge lies in the subgraph. -/
private theorem chain3Matching_mem_left :
    s(Sum.inl (0 : Fin 3), Sum.inr 1) ∈ chain3Matching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The second explicit chain edge lies in the subgraph. -/
private theorem chain3Matching_mem_right :
    s(Sum.inl (1 : Fin 3), Sum.inr 2) ∈ chain3Matching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The two explicit chain edges are distinct. -/
private theorem chain3Matching_edges_ne :
    s(Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3)) ≠
      s(Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- Every matching subgraph of the chain double cover has at most 2 edges:
every arc touches vertex `1` on one side. -/
private theorem chain3_subgraph_matching_ncard_le
    (M' : (doubleCover chain3).Subgraph) (hM' : M'.IsMatching) :
    M'.edgeSet.ncard ≤ 2 := by
  have : Finite (Sym2 (Fin 3 ⊕ Fin 3)) := Quot.finite _
  have hcover : M'.edgeSet ⊆ {e ∈ M'.edgeSet | Sum.inl 1 ∈ e} ∪
      {e ∈ M'.edgeSet | Sum.inr 1 ∈ e} := by
    intro e he
    obtain ⟨u, v, hadj, rfl⟩ := edge_eq_cross_of_mem M' he
    rw [chain3_adj_iff] at hadj
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
    · exact Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inl rfl⟩
  have h1 := ncard_edges_at_vertex_le_one M' hM' (Sum.inl (1 : Fin 3))
  have h2 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (1 : Fin 3))
  have hle := Set.ncard_le_ncard hcover (Set.toFinite _)
  have hunion := Set.ncard_union_le {e ∈ M'.edgeSet | Sum.inl 1 ∈ e}
    {e ∈ M'.edgeSet | Sum.inr 1 ∈ e}
  omega

/-- The explicit chain matching has 2 edges. -/
private theorem chain3Matching_ncard_eq :
    chain3Matching.edgeSet.ncard = 2 := by
  have : Finite (Sym2 (Fin 3 ⊕ Fin 3)) := Quot.finite _
  have hsub : ({s(Sum.inl (0 : Fin 3), Sum.inr 1),
      s(Sum.inl 1, Sum.inr (2 : Fin 3))} : Set _) ⊆
      chain3Matching.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact chain3Matching_mem_left
    · exact chain3Matching_mem_right
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair chain3Matching_edges_ne] at hle
  have hub := chain3_subgraph_matching_ncard_le _ chain3Matching_isMatching
  omega

/-- The explicit 2-edge chain matching is maximum. -/
private theorem chain3Matching_isMaximum :
    IsMaximumMatching (doubleCover chain3) chain3Matching :=
  ⟨chain3Matching_isMatching, fun M' hM' => by
    rw [chain3Matching_ncard_eq]
    exact chain3_subgraph_matching_ncard_le M' hM'⟩

/-- The minimum path cover of the non-transitive chain is one path. -/
example : minPathCoverSize chain3 = 1 := by
  have h := minPathCover_eq_card_sub_ncard_maximum chain3 chain3_dag
    chain3Matching_isMaximum
  rw [chain3Matching_ncard_eq, Fintype.card_fin] at h
  exact h

/-- An explicit 2-edge matching subgraph of the chain-closure double cover,
over the reachability arcs `(0, 1)` and `(1, 2)`. -/
private abbrev chain3ClosureMatching :
    (doubleCover (transClosure chain3)).Subgraph where
  verts := {Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 2}
  Adj := fun x y =>
    (x = Sum.inl 0 ∧ y = Sum.inr 1) ∨ (x = Sum.inr 1 ∧ y = Sum.inl 0) ∨
    (x = Sum.inl 1 ∧ y = Sum.inr 2) ∨ (x = Sum.inr 2 ∧ y = Sum.inl 1)
  adj_sub := by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Relation.TransGen chain3.Adj 0 1
      exact Relation.TransGen.single (by decide)
    · show Relation.TransGen chain3.Adj 0 1
      exact Relation.TransGen.single (by decide)
    · show Relation.TransGen chain3.Adj 1 2
      exact Relation.TransGen.single (by decide)
    · show Relation.TransGen chain3.Adj 1 2
      exact Relation.TransGen.single (by decide)
  edge_vert := by
    intro x y h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  symm := ⟨by
    intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide⟩

/-- The explicit chain-closure subgraph is a matching. -/
private theorem chain3ClosureMatching_isMatching :
    chain3ClosureMatching.IsMatching := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨Sum.inr 1, by decide, by decide⟩
  · exact ⟨Sum.inr 2, by decide, by decide⟩
  · exact ⟨Sum.inl 0, by decide, by decide⟩
  · exact ⟨Sum.inl 1, by decide, by decide⟩

/-- The first explicit chain-closure edge lies in the subgraph. -/
private theorem chain3ClosureMatching_mem_left :
    s(Sum.inl (0 : Fin 3), Sum.inr 1) ∈
      chain3ClosureMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The second explicit chain-closure edge lies in the subgraph. -/
private theorem chain3ClosureMatching_mem_right :
    s(Sum.inl (1 : Fin 3), Sum.inr 2) ∈
      chain3ClosureMatching.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  decide

/-- The two explicit chain-closure edges are distinct. -/
private theorem chain3ClosureMatching_edges_ne :
    s(Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3)) ≠
      s(Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- Every matching subgraph of the chain-closure double cover has at most 2
edges: nothing reaches `0`, so every edge passes through `Sum.inr 1` or
`Sum.inr 2`. -/
private theorem chain3Closure_subgraph_matching_ncard_le
    (M' : (doubleCover (transClosure chain3)).Subgraph)
    (hM' : M'.IsMatching) : M'.edgeSet.ncard ≤ 2 := by
  have : Finite (Sym2 (Fin 3 ⊕ Fin 3)) := Quot.finite _
  have hcover : M'.edgeSet ⊆ {e ∈ M'.edgeSet | Sum.inr 1 ∈ e} ∪
      {e ∈ M'.edgeSet | Sum.inr 2 ∈ e} := by
    intro e he
    obtain ⟨u, v, hadj, rfl⟩ := edge_eq_cross_of_mem M' he
    fin_cases v
    · exact (chain3_no_transGen_to_zero u hadj).elim
    · exact Or.inl ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
    · exact Or.inr ⟨he, by rw [Sym2.mem_iff]; exact Or.inr rfl⟩
  have h1 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (1 : Fin 3))
  have h2 := ncard_edges_at_vertex_le_one M' hM' (Sum.inr (2 : Fin 3))
  have hle := Set.ncard_le_ncard hcover (Set.toFinite _)
  have hunion := Set.ncard_union_le {e ∈ M'.edgeSet | Sum.inr 1 ∈ e}
    {e ∈ M'.edgeSet | Sum.inr 2 ∈ e}
  omega

/-- The explicit chain-closure matching has 2 edges. -/
private theorem chain3ClosureMatching_ncard_eq :
    chain3ClosureMatching.edgeSet.ncard = 2 := by
  have : Finite (Sym2 (Fin 3 ⊕ Fin 3)) := Quot.finite _
  have hsub : ({s(Sum.inl (0 : Fin 3), Sum.inr 1),
      s(Sum.inl 1, Sum.inr (2 : Fin 3))} : Set _) ⊆
      chain3ClosureMatching.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact chain3ClosureMatching_mem_left
    · exact chain3ClosureMatching_mem_right
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair chain3ClosureMatching_edges_ne] at hle
  have hub := chain3Closure_subgraph_matching_ncard_le _
    chain3ClosureMatching_isMatching
  omega

/-- The explicit 2-edge chain-closure matching is maximum. -/
private theorem chain3ClosureMatching_isMaximum :
    IsMaximumMatching (doubleCover (transClosure chain3))
      chain3ClosureMatching :=
  ⟨chain3ClosureMatching_isMatching, fun M' hM' => by
    rw [chain3ClosureMatching_ncard_eq]
    exact chain3Closure_subgraph_matching_ncard_le M' hM'⟩

/-- The reachability width of the chain is 1. -/
example : maxAntichainSize (transClosure chain3)
    (isTransitiveDAG_transClosure chain3 chain3_dag) = 1 := by
  have h := width_eq_card_sub_ncard_maximum_transClosure chain3 chain3_dag
    chain3ClosureMatching_isMaximum
  rw [chain3ClosureMatching_ncard_eq, Fintype.card_fin] at h
  exact h

/-- Coincidence on a non-transitive DAG: the chain needs one path, and its
transitive closure also needs one path (via Dilworth on the width-1
closure). -/
example : minPathCoverSize chain3 = 1 ∧
    minPathCoverSize (transClosure chain3) = 1 := by
  have hchain := minPathCover_eq_card_sub_ncard_maximum chain3 chain3_dag
    chain3Matching_isMaximum
  rw [chain3Matching_ncard_eq, Fintype.card_fin] at hchain
  have hwidth := width_eq_card_sub_ncard_maximum_transClosure chain3 chain3_dag
    chain3ClosureMatching_isMaximum
  rw [chain3ClosureMatching_ncard_eq, Fintype.card_fin] at hwidth
  have hdil := minPathCover_eq_maxAntichain (transClosure chain3)
    (isTransitiveDAG_transClosure chain3 chain3_dag)
  omega

end MathlibExtTest.Combinatorics.SimpleGraph.PathCoverGeneral
