/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`;
maximum-matching section split from GallaiEdmonds.lean.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `e369bf2e` (PR #5951).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MathlibExt.Combinatorics.Matching

/-!
# Maximum matchings

A matching subgraph is maximum when no matching subgraph has more edges.
This module provides the maximum-matching predicate, its basic facts,
and existence of a maximum matching on a finite graph, split from the
Gallai–Edmonds development which builds the D/A/C decomposition on top
of it.
-/

variable {V : Type*}

/-! ## Maximum matchings -/

/-- A matching subgraph is *maximum* if no matching subgraph has more edges.
The vertex type is required to be finite: `Set.ncard` comparisons between
matchings are meaningless on infinite graphs (all infinite edge sets have
`ncard` zero). -/
@[nolint unusedArguments]
def IsMaximumMatching [Finite V] (G : SimpleGraph V) (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- A maximum matching is a matching. -/
theorem IsMaximumMatching.isMatching [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (h : IsMaximumMatching G M) : M.IsMatching :=
  h.1

/-- Maximality of the edge count of a maximum matching. -/
theorem IsMaximumMatching.le_ncard [Finite V] {G : SimpleGraph V} {M M' : G.Subgraph}
    (h : IsMaximumMatching G M) (hM' : M'.IsMatching) :
    M'.edgeSet.ncard ≤ M.edgeSet.ncard :=
  h.2 M' hM'

/-- All maximum matchings have the same number of edges. -/
theorem IsMaximumMatching.ncard_eq [Finite V] {G : SimpleGraph V} {M M' : G.Subgraph}
    (h : IsMaximumMatching G M) (h' : IsMaximumMatching G M') :
    M.edgeSet.ncard = M'.edgeSet.ncard :=
  le_antisymm (h'.le_ncard h.isMatching) (h.le_ncard h'.isMatching)

/-- A `Finset` of edges is a matching for `G` if its edges lie in `G` and are
pairwise vertex-disjoint (the `BergeLemma` vocabulary). -/
private def IsFinMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂

/-- The subgraph spanned by a `Finset` matching. -/
private def subgraphOfFinset (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet) : G.Subgraph where
  verts := {v | ∃ e ∈ M, v ∈ e}
  Adj v w := s(v, w) ∈ M
  adj_sub {v w} h := (SimpleGraph.mem_edgeSet G).mp (hG _ h)
  edge_vert {v w} h := ⟨s(v, w), h, Sym2.mem_mk_left v w⟩
  symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩

/-- The edge set of `subgraphOfFinset` is the coercion of `M`. -/
private theorem edgeSet_subgraphOfFinset (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet) :
    (subgraphOfFinset G M hG).edgeSet = (↑M : Set (Sym2 V)) := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  simp only [SimpleGraph.Subgraph.mem_edgeSet, Finset.mem_coe]
  rfl

/-- A `Finset` matching gives an `IsMatching` subgraph. -/
private theorem isMatching_subgraphOfFinset (G : SimpleGraph V) (M : Finset (Sym2 V))
    (h : IsFinMatching G M) : (subgraphOfFinset G M h.1).IsMatching := by
  intro v hv
  obtain ⟨e, heM, hve⟩ := hv
  refine ⟨Sym2.Mem.other hve, ?_, ?_⟩
  · change s(v, Sym2.Mem.other hve) ∈ M
    rw [Sym2.other_spec hve]
    exact heM
  · intro w hw
    have hwsM : s(v, w) ∈ M := hw
    have heq : s(v, w) = e := by
      by_contra hne
      exact (h.2 e heM s(v, w) hwsM (Ne.symm hne) v hve) (Sym2.mem_mk_left v w)
    have hne : v ≠ w := by
      have hadj : G.Adj v w := (SimpleGraph.mem_edgeSet G).mp (h.1 _ hwsM)
      exact hadj.ne
    have hwmem : w ∈ e := heq ▸ Sym2.mem_mk_right v w
    rw [← Sym2.other_spec hve] at hwmem
    rcases Sym2.mem_iff.mp hwmem with h' | h'
    · exact absurd h'.symm hne
    · exact h'

/-- Edge count of `subgraphOfFinset`. -/
private theorem ncard_edgeSet_subgraphOfFinset (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) :
    (subgraphOfFinset G M hG).edgeSet.ncard = M.card := by
  rw [edgeSet_subgraphOfFinset, Set.ncard_coe_finset]

/-- An `IsMatching` subgraph gives a `Finset` matching. -/
private theorem isFinMatching_edgeSet_toFinset (G : SimpleGraph V)
    {M : G.Subgraph} (hM : M.IsMatching) [Fintype (M.edgeSet : Set (Sym2 V))] :
    IsFinMatching G M.edgeSet.toFinset := by
  constructor
  · intro e he
    rw [Set.mem_toFinset] at he
    exact M.edgeSet_subset he
  · intro e₁ he₁ e₂ he₂ hne v hv1 hv2
    rw [Set.mem_toFinset] at he₁ he₂
    obtain ⟨a, b⟩ := e₁
    obtain ⟨c, d⟩ := e₂
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he₁ he₂
    rcases Sym2.mem_iff.mp hv1 with rfl | rfl
    · rcases Sym2.mem_iff.mp hv2 with h | h
      · subst h
        have hbd : b = d := hM.eq_of_adj_left he₁ he₂
        subst hbd
        exact hne rfl
      · subst h
        have hbc : b = c := hM.eq_of_adj_left he₁ (M.adj_symm he₂)
        subst hbc
        exact hne Sym2.eq_swap
    · rcases Sym2.mem_iff.mp hv2 with h | h
      · subst h
        have hac : a = d := hM.eq_of_adj_left (M.adj_symm he₁) he₂
        subst hac
        exact hne Sym2.eq_swap
      · subst h
        have hac : a = c :=
          hM.eq_of_adj_left (M.adj_symm he₁) (M.adj_symm he₂)
        subst hac
        exact hne rfl

/-- Every finite graph has a maximum matching (maximize over the finite set of
`Finset` matchings). -/
theorem exists_maximum_matching [Finite V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, IsMaximumMatching G M := by
  classical
  have := Fintype.ofFinite V
  have : Finite (Sym2 V) := Quot.finite _
  have := Fintype.ofFinite (Sym2 V)
  set E := G.edgeSet.toFinset with hEdef
  have hnonempty :
      (E.powerset.filter (fun F => IsFinMatching G F)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    refine ⟨fun e he => absurd he (Finset.notMem_empty e), fun e₁ he₁ => ?_⟩
    exact absurd he₁ (Finset.notMem_empty e₁)
  obtain ⟨M0, hM0mem, hM0max⟩ :=
    Finset.exists_max_image _ (fun F => F.card) hnonempty
  have hM0fin : IsFinMatching G M0 := (Finset.mem_filter.mp hM0mem).2
  refine ⟨subgraphOfFinset G M0 hM0fin.1,
    isMatching_subgraphOfFinset G M0 hM0fin, ?_⟩
  intro M' hM'
  have hM'fin : IsFinMatching G M'.edgeSet.toFinset :=
    isFinMatching_edgeSet_toFinset G hM'
  have hmem :
      M'.edgeSet.toFinset ∈ E.powerset.filter (fun F => IsFinMatching G F) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hM'fin⟩
    intro e he
    rw [Set.mem_toFinset] at he
    rw [hEdef, Set.mem_toFinset]
    exact M'.edgeSet_subset he
  have hle := hM0max _ hmem
  rw [ncard_edgeSet_subgraphOfFinset, Set.ncard_eq_toFinset_card']
  exact hle

end MathlibExt.Combinatorics.Matching
