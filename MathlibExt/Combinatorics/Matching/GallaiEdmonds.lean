/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `e369bf2e` (PR #5951).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Sym.Sym2
public import MathlibExt.Combinatorics.Matching.MaximumMatching

@[expose] public section

namespace MathlibExt.Combinatorics.Matching.GallaiEdmonds

/-!
# Gallai–Edmonds decomposition (Diestel §2.2 in the 5th edition (§2.3 in the 4th))

For a finite graph `G`, the Gallai–Edmonds decomposition partitions the vertex
set into three parts:

* `D` (`gallaiD`): vertices missed by *some* maximum matching;
* `A` (`gallaiA`): the neighbors of `D` outside `D`;
* `C` (`gallaiC`): all remaining vertices.

The Gallai–Edmonds structure theorem (Diestel Theorem 2.2.3 in the 5th edition (Theorem 2.3.1 in
the 4th)) states that the
components of `G[D]` are factor-critical (`IsFactorCritical`), that `G[C]` has
a perfect matching, and that every maximum matching matches `A` into distinct
components of `G[D]`; the Tutte–Berge deficiency formula
`def(G) = c(D) - |A|` follows by counting.

This module provides the `D`/`A`/`C` definitions on top of the `BergeLemma`
matching vocabulary (`SimpleGraph.Subgraph` matchings measured by
`edgeSet.ncard`), proves the basic structural facts (partition, no edges
between `C` and `D`, vertices outside `D` covered by every maximum matching),
develops factor-critical graphs (odd order) and the matching-deficiency
calculus including the easy direction of the Tutte–Berge inequality, and
states a deliberately weakened structural hypothesis as
`IsGallaiEdmondsDecomp` (one arbitrary A-to-D matching, not quantification
over every maximum matching) with its immediate conditional counting
corollaries; see the weakening note at the declaration.

Scope note: the unconditional proof of the structure theorem (factor-critical
`D`-components, perfect matching on `C`) requires alternating-tree / barrier
machinery beyond this module and is left as future work; the statements here
are the machine-checked-correct conditional forms.
-/

variable {V : Type*}

open MathlibExt.Combinatorics.Matching

/-! ## The Gallai–Edmonds sets `D`, `A`, `C` -/

/-- The Gallai–Edmonds set `D`: vertices missed by *some* maximum matching. -/
def gallaiD [Finite V] (G : SimpleGraph V) : Set V :=
  {v | ∃ M : G.Subgraph, IsMaximumMatching G M ∧ v ∉ M.verts}

/-- The Gallai–Edmonds set `A`: neighbors of `D` outside `D`. -/
def gallaiA [Finite V] (G : SimpleGraph V) : Set V :=
  {w | w ∉ gallaiD G ∧ ∃ v ∈ gallaiD G, G.Adj v w}

/-- The Gallai–Edmonds set `C`: all remaining vertices. -/
def gallaiC [Finite V] (G : SimpleGraph V) : Set V :=
  (gallaiD G ∪ gallaiA G)ᶜ

/-- Membership in `D`. -/
theorem mem_gallaiD [Finite V] (G : SimpleGraph V) (v : V) :
    v ∈ gallaiD G ↔ ∃ M : G.Subgraph, IsMaximumMatching G M ∧ v ∉ M.verts :=
  Iff.rfl

/-- Membership in `A`. -/
theorem mem_gallaiA [Finite V] (G : SimpleGraph V) (w : V) :
    w ∈ gallaiA G ↔ w ∉ gallaiD G ∧ ∃ v ∈ gallaiD G, G.Adj v w :=
  Iff.rfl

/-- Membership in `C`. -/
theorem mem_gallaiC [Finite V] (G : SimpleGraph V) (c : V) :
    c ∈ gallaiC G ↔ c ∉ gallaiD G ∧ c ∉ gallaiA G := by
  simp [gallaiC]

/-- `D`, `A`, `C` cover all vertices. -/
theorem gallai_partition [Finite V] (G : SimpleGraph V) :
    gallaiD G ∪ gallaiA G ∪ gallaiC G = Set.univ := by
  ext v
  simp only [gallaiC, Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
  exact em _

/-- `D` and `A` are disjoint. -/
theorem disjoint_gallaiD_gallaiA [Finite V] (G : SimpleGraph V) :
    Disjoint (gallaiD G) (gallaiA G) := by
  rw [Set.disjoint_left]
  intro v hvD hvA
  rw [mem_gallaiA] at hvA
  exact hvA.1 hvD

/-- `D` and `C` are disjoint. -/
theorem disjoint_gallaiD_gallaiC [Finite V] (G : SimpleGraph V) :
    Disjoint (gallaiD G) (gallaiC G) := by
  rw [Set.disjoint_left]
  intro v hvD hvC
  rw [mem_gallaiC] at hvC
  exact hvC.1 hvD

/-- `A` and `C` are disjoint. -/
theorem disjoint_gallaiA_gallaiC [Finite V] (G : SimpleGraph V) :
    Disjoint (gallaiA G) (gallaiC G) := by
  rw [Set.disjoint_left]
  intro v hvA hvC
  rw [mem_gallaiC] at hvC
  exact hvC.2 hvA

/-- A neighbor of `D` outside `D` lies in `A`. -/
theorem mem_gallaiA_of_adj [Finite V] (G : SimpleGraph V) {v w : V}
    (hv : v ∈ gallaiD G) (hadj : G.Adj v w) (hw : w ∉ gallaiD G) :
    w ∈ gallaiA G := by
  rw [mem_gallaiA]
  exact ⟨hw, v, hv, hadj⟩

/-- There are no edges between `C` and `D`: every neighbor of `D` outside `D`
lies in `A`. -/
theorem no_adj_gallaiC_gallaiD [Finite V] (G : SimpleGraph V) {c d : V}
    (hc : c ∈ gallaiC G) (hd : d ∈ gallaiD G) : ¬ G.Adj c d := by
  rw [mem_gallaiC] at hc
  obtain ⟨hcD, hcA⟩ := hc
  intro hadj
  apply hcA
  rw [mem_gallaiA]
  exact ⟨hcD, d, hd, hadj.symm⟩

/-- Vertices outside `D` are covered by every maximum matching. -/
theorem covered_of_notMem_gallaiD [Finite V] (G : SimpleGraph V) {M : G.Subgraph}
    (hM : IsMaximumMatching G M) {v : V} (hv : v ∉ gallaiD G) : v ∈ M.verts := by
  by_contra hcon
  rw [mem_gallaiD] at hv
  exact hv ⟨M, hM, hcon⟩

/-- `A` is covered by every maximum matching. -/
theorem gallaiA_subset_verts [Finite V] (G : SimpleGraph V) {M : G.Subgraph}
    (hM : IsMaximumMatching G M) {a : V} (ha : a ∈ gallaiA G) : a ∈ M.verts := by
  rw [mem_gallaiA] at ha
  exact covered_of_notMem_gallaiD G hM ha.1

/-- `C` is covered by every maximum matching. -/
theorem gallaiC_subset_verts [Finite V] (G : SimpleGraph V) {M : G.Subgraph}
    (hM : IsMaximumMatching G M) {c : V} (hc : c ∈ gallaiC G) : c ∈ M.verts := by
  rw [mem_gallaiC] at hc
  exact covered_of_notMem_gallaiD G hM hc.1

/-! ## Factor-critical graphs -/

/-- A graph is *factor-critical* if deleting any single vertex leaves a graph
with a perfect matching. -/
def IsFactorCritical (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ M : (G.induce {v}ᶜ).Subgraph, M.IsPerfectMatching

/-- A nonempty finite factor-critical graph has odd order: deleting one vertex
leaves an even-order graph with a perfect matching. -/
theorem IsFactorCritical.odd_card [Finite V] [Nonempty V] {G : SimpleGraph V}
    (h : IsFactorCritical G) : Odd (Nat.card V) := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨v⟩ : Nonempty V := inferInstance
  obtain ⟨M, hM⟩ := h v
  have heven := hM.even_card
  have hcard : (({v}ᶜ : Set V)).ncard + 1 = Nat.card V := by
    have hdisj : Disjoint (({v}ᶜ : Set V)) ({v} : Set V) :=
      Set.disjoint_left.mpr (fun x hx hx' => hx hx')
    have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [Set.compl_union_self, Set.ncard_univ, Set.ncard_singleton] at h
    omega
  have h2 : Fintype.card (↥(({v}ᶜ : Set V))) = (({v}ᶜ : Set V)).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [h2] at heven
  obtain ⟨k, hk⟩ := heven
  refine ⟨k, by omega⟩

/-- A graph on at most one vertex is factor-critical: deleting the vertex
leaves the empty graph, perfectly matched by the empty matching. -/
theorem isFactorCritical_of_subsingleton [Subsingleton V] (G : SimpleGraph V) :
    IsFactorCritical G := by
  intro v
  have : IsEmpty {x // x ∈ ({v}ᶜ : Set V)} :=
    ⟨fun x => (x.2) (by simp [Subsingleton.elim x.1 v])⟩
  refine ⟨⊥, ?_, ?_⟩
  · intro x _
    exact (IsEmpty.false x).elim
  · intro x
    exact (IsEmpty.false x).elim

/-! ## Matching counting -/

/-- The vertex set of a matching has twice as many vertices as edges. -/
theorem matching_verts_ncard_eq [Finite V] (G : SimpleGraph V)
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have : Finite (Sym2 V) := Quot.finite _
  have := Fintype.ofFinite (Sym2 V)
  set C := M.edgeSet.toFinset.biUnion Sym2.toFinset with hCdef
  have hCeq : (↑C : Set V) = M.verts := by
    ext v
    rw [hCdef]
    simp only [Finset.mem_coe, Finset.mem_biUnion, Sym2.mem_toFinset]
    constructor
    · rintro ⟨e, he, hve⟩
      rw [Set.mem_toFinset] at he
      exact M.mem_verts_of_mem_edge he hve
    · intro hv
      obtain ⟨w, hvw, -⟩ := hM hv
      refine ⟨s(v, w), ?_, Sym2.mem_mk_left v w⟩
      rw [Set.mem_toFinset]
      exact SimpleGraph.Subgraph.mem_edgeSet.mpr hvw
  have hdisj :
      (↑M.edgeSet.toFinset : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨x, y⟩ := e₁
    obtain ⟨p, q⟩ := e₂
    rw [Finset.mem_coe, Set.mem_toFinset] at he₁ he₂
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he₁ he₂
    refine Finset.disjoint_left.mpr fun a ha1 ha2 => ?_
    rw [Sym2.mem_toFinset] at ha1 ha2
    rcases Sym2.mem_iff.mp ha1 with rfl | rfl
    · rcases Sym2.mem_iff.mp ha2 with h | h
      · subst h
        have hbd : y = q := hM.eq_of_adj_left he₁ he₂
        subst hbd
        exact hne rfl
      · subst h
        have hbc : y = p := hM.eq_of_adj_left he₁ (M.adj_symm he₂)
        subst hbc
        exact hne Sym2.eq_swap
    · rcases Sym2.mem_iff.mp ha2 with h | h
      · subst h
        have hac : x = q := hM.eq_of_adj_left (M.adj_symm he₁) he₂
        subst hac
        exact hne Sym2.eq_swap
      · subst h
        have hac : x = p :=
          hM.eq_of_adj_left (M.adj_symm he₁) (M.adj_symm he₂)
        subst hac
        exact hne rfl
  have h2 : ∀ e ∈ M.edgeSet.toFinset, (Sym2.toFinset e).card = 2 := by
    intro e he
    rw [Set.mem_toFinset] at he
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset he))
  have hcard : C.card = 2 * M.edgeSet.toFinset.card := by
    rw [hCdef, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
    exact mul_comm _ _
  rw [← hCeq, Set.ncard_coe_finset, hcard, Set.ncard_eq_toFinset_card']

/-- Exposed vertices plus twice the matching size equals the order of the
graph. -/
theorem matching_exposed_add [Finite V] (G : SimpleGraph V) {M : G.Subgraph}
    (hM : M.IsMatching) :
    (M.vertsᶜ).ncard + 2 * M.edgeSet.ncard = Nat.card V := by
  have hfin : M.verts.Finite := Set.toFinite _
  have hdisj : Disjoint M.verts M.vertsᶜ :=
    Set.disjoint_left.mpr (fun x hx hx' => hx' hx)
  have h := Set.ncard_union_eq hdisj hfin (Set.toFinite _)
  rw [Set.union_compl_self, Set.ncard_univ] at h
  rw [matching_verts_ncard_eq G hM] at h
  omega

/-! ## Deficiency and the Tutte–Berge inequality -/

/-- The *deficiency* of `G`: the number of vertices left exposed by a maximum
matching. -/
noncomputable def matchingDeficiency [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card V - 2 * (Classical.choose (exists_maximum_matching G)).edgeSet.ncard

/-- The deficiency in terms of any maximum matching. -/
theorem deficiency_eq_of_isMaximum [Finite V] (G : SimpleGraph V)
    {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    matchingDeficiency G = Nat.card V - 2 * M.edgeSet.ncard := by
  unfold matchingDeficiency
  rw [hM.ncard_eq (Classical.choose_spec (exists_maximum_matching G))]

/-- The deficiency equals the number of vertices exposed by any maximum
matching. -/
theorem deficiency_eq_exposed_of_isMaximum [Finite V] (G : SimpleGraph V)
    {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    matchingDeficiency G = (M.vertsᶜ).ncard := by
  rw [deficiency_eq_of_isMaximum G hM]
  have h := matching_exposed_add G hM.isMatching
  omega

/-- **Tutte–Berge inequality (easy direction).** The number of odd components
of `G - u` is at most the number of `M`-exposed vertices plus `|u|`, for any
matching `M`. Each odd component either contains an exposed vertex or is
matched by `M` into `u` (else the matching would restrict to a pairing of an
odd set); distinct components give distinct witnesses. -/
theorem tutteBerge_odd_le [Finite V] (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (u : Set V) :
    (((⊤ : G.Subgraph).deleteVerts u).coe).oddComponents.ncard ≤
      (M.vertsᶜ).ncard + u.ncard := by
  classical
  have := Fintype.ofFinite V
  have hverts : ((⊤ : G.Subgraph).deleteVerts u).verts = Set.univ \ u := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top]
  set Dsub := (⊤ : G.Subgraph).deleteVerts u with hDdef
  have hmem_out : ∀ x : ↥Dsub.verts, (x : V) ∉ u := by
    intro x
    have hx : (x : V) ∈ Set.univ \ u := by
      rw [← hverts]
      exact x.2
    rw [Set.mem_sdiff] at hx
    exact hx.2
  have htop : ∀ v : V, v ∈ (⊤ : G.Subgraph).verts := fun v => by
    rw [SimpleGraph.Subgraph.verts_top]
    trivial
  -- Matching edges with both ends outside `u` stay inside one component.
  have hstay : ∀ x : ↥Dsub.verts, ∀ c : Dsub.coe.ConnectedComponent,
      x ∈ c.supp → ∀ w : V, M.Adj (x : V) w → w ∉ u →
        ∃ y ∈ c.supp, (y : V) = w := by
    intro x c hxs w hadj hwu
    have hwmem : w ∈ Dsub.verts := by
      rw [hverts, Set.mem_sdiff]
      exact ⟨Set.mem_univ w, hwu⟩
    have hxnu : (x : V) ∉ u := hmem_out x
    have hdel : Dsub.Adj (x : V) w := by
      change ((⊤ : G.Subgraph).deleteVerts u).Adj (x : V) w
      exact SimpleGraph.Subgraph.deleteVerts_adj.mpr
        ⟨htop _, hxnu, htop _, hwu,
          SimpleGraph.Subgraph.top_adj.mpr (M.adj_sub hadj)⟩
    have hcoe : Dsub.coe.Adj x ⟨w, hwmem⟩ :=
      SimpleGraph.Subgraph.Adj.coe hdel
    have hmem2 := c.mem_supp_of_adj_mem_supp hxs hcoe
    exact ⟨⟨w, hwmem⟩, hmem2, rfl⟩
  -- For each odd component, a witness vertex in `vertsᶜ ∪ u`.
  have hwit : ∀ c : Dsub.coe.ConnectedComponent, c ∈ Dsub.coe.oddComponents →
      ∃ t : V, t ∈ M.vertsᶜ ∪ u ∧
        ((∃ x ∈ c.supp, (x : V) = t ∧ t ∉ M.verts) ∨
          (t ∈ u ∧ ∃ x ∈ c.supp, M.Adj (x : V) t)) := by
    intro c hc
    have hodd : Odd c.supp.ncard := hc
    by_cases hexp : ∃ x ∈ c.supp, (x : V) ∉ M.verts
    · obtain ⟨x, hxs, hxexp⟩ := hexp
      exact ⟨(x : V), Or.inl hxexp, Or.inl ⟨x, hxs, rfl, hxexp⟩⟩
    · have hcov : ∀ x ∈ c.supp, (x : V) ∈ M.verts := by
        intro x hxs
        by_contra hcon
        exact hexp ⟨x, hxs, hcon⟩
      by_cases hpart : ∃ x ∈ c.supp, ∃ w ∈ u, M.Adj (x : V) w
      · obtain ⟨x, hxs, w, hwu, hadj⟩ := hpart
        exact ⟨w, Or.inr hwu, Or.inr ⟨hwu, x, hxs, hadj⟩⟩
      · exfalso
        -- Every vertex covered, every partner outside `u`: parity contradiction.
        set S := Subtype.val '' c.supp with hSdef
        have hSodd : Odd S.ncard := by
          rw [hSdef, Set.ncard_image_of_injective _ (fun a b h => Subtype.ext h)]
          exact hodd
        have hSstay : ∀ x ∈ c.supp, ∀ w : V, M.Adj (x : V) w → w ∈ S := by
          intro x hxs w hadj
          by_cases hwu : w ∈ u
          · exfalso
            exact hpart ⟨x, hxs, w, hwu, hadj⟩
          · obtain ⟨y, hys, rfl⟩ := hstay x c hxs w hadj hwu
            exact ⟨y, hys, rfl⟩
        -- The matching restricts to a pairing of the odd set `S`.
        obtain ⟨M', hM'verts, hM'match⟩ :
            ∃ M' : G.Subgraph, M'.verts = S ∧ M'.IsMatching := by
          refine ⟨{ verts := S
                    Adj := fun a b => M.Adj a b ∧ a ∈ S ∧ b ∈ S
                    adj_sub := fun h => M.adj_sub h.1
                    edge_vert := fun h => h.2.1
                    symm := ⟨fun a b h => ⟨M.adj_symm h.1, h.2.2, h.2.1⟩⟩ },
            rfl, ?_⟩
          intro s hs
          obtain ⟨x, hxs, rfl⟩ := hs
          obtain ⟨w, hwadj, huniq⟩ := hM (hcov x hxs)
          have hwS : w ∈ S := hSstay x hxs w hwadj
          refine ⟨w, ⟨hwadj, ⟨x, hxs, rfl⟩, hwS⟩, ?_⟩
          intro w' hw'
          exact huniq w' hw'.1
        have heven : Even M'.verts.toFinset.card := hM'match.even_card
        rw [hM'verts, ← Set.ncard_eq_toFinset_card'] at heven
        obtain ⟨k, hk⟩ := hSodd
        obtain ⟨j, hj⟩ := heven
        omega
  -- Assemble the witnesses into an injective map.
  by_cases hV : Nonempty V
  · have hwit' : ∀ c : Dsub.coe.ConnectedComponent,
        ∃ t : V, c ∈ Dsub.coe.oddComponents →
          t ∈ M.vertsᶜ ∪ u ∧
            ((∃ x ∈ c.supp, (x : V) = t ∧ t ∉ M.verts) ∨
              (t ∈ u ∧ ∃ x ∈ c.supp, M.Adj (x : V) t)) := by
      intro c
      by_cases hc : c ∈ Dsub.coe.oddComponents
      · obtain ⟨t, ht⟩ := hwit c hc
        exact ⟨t, fun _ => ht⟩
      · exact ⟨Classical.choice hV, fun h => absurd h hc⟩
    choose F hF using hwit'
    have hinj : Set.InjOn F Dsub.coe.oddComponents := by
      intro c₁ hc₁ c₂ hc₂ heq
      have h1 := hF c₁ hc₁
      have h2 := hF c₂ hc₂
      rcases h1 with ⟨-, h1⟩
      rcases h2 with ⟨-, h2⟩
      rcases h1 with ⟨x₁, hx₁s, e₁, hx₁exp⟩ | ⟨hw₁u, x₁, hx₁s, hadj₁⟩ <;>
        rcases h2 with ⟨x₂, hx₂s, e₂, hx₂exp⟩ | ⟨hw₂u, x₂, hx₂s, hadj₂⟩
      · -- Both witnesses exposed: they lie in one component.
        have hx : x₁ = x₂ := Subtype.ext (e₁.trans (heq.trans e₂.symm))
        subst hx
        by_contra hne
        have hdisj :=
          SimpleGraph.pairwise_disjoint_supp_connectedComponent Dsub.coe hne
        exact (Set.disjoint_left.mp hdisj hx₁s) hx₂s
      · -- Exposed meets matched: contradiction.
        exfalso
        have hadj₂' : M.Adj (x₂ : V) (F c₁) := by
          rw [heq]
          exact hadj₂
        exact hx₁exp (M.edge_vert (M.adj_symm hadj₂'))
      · -- Matched meets exposed: contradiction.
        exfalso
        have hadj₁' : M.Adj (x₁ : V) (F c₂) := by
          rw [← heq]
          exact hadj₁
        exact hx₂exp (M.edge_vert (M.adj_symm hadj₁'))
      · -- Both witnesses matched: unique partners lie in one component.
        have hadj₂' : M.Adj (x₂ : V) (F c₁) := by
          rw [heq]
          exact hadj₂
        have hx : x₁ = x₂ :=
          Subtype.ext (hM.eq_of_adj_right hadj₁ hadj₂')
        subst hx
        by_contra hne
        have hdisj :=
          SimpleGraph.pairwise_disjoint_supp_connectedComponent Dsub.coe hne
        exact (Set.disjoint_left.mp hdisj hx₁s) hx₂s
    have hle := Set.ncard_le_ncard_of_injOn F (fun c hc => (hF c hc).1) hinj
      (Set.toFinite _)
    exact le_trans hle (Set.ncard_union_le _ _)
  · -- No vertices: no odd components.
    have hempty : Dsub.coe.oddComponents = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨x, -⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
      exact hV ⟨(x : V)⟩
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _

/-- The deficiency is at least the Tutte–Berge surplus of any vertex set. -/
theorem tutteBerge_deficiency_ge [Finite V] (G : SimpleGraph V) (u : Set V) :
    (((⊤ : G.Subgraph).deleteVerts u).coe).oddComponents.ncard ≤
      matchingDeficiency G + u.ncard := by
  obtain ⟨M, hM⟩ := exists_maximum_matching G
  have h := tutteBerge_odd_le G M hM.isMatching u
  have hdef := deficiency_eq_exposed_of_isMaximum G hM
  omega

/-! ## The Gallai–Edmonds structure theorem statement -/

/-- The subgraph induced by the Gallai–Edmonds set `D`. -/
def gallaiGraphD [Finite V] (G : SimpleGraph V) :
    SimpleGraph ↥(((⊤ : G.Subgraph).deleteVerts (gallaiD G)ᶜ).verts) :=
  ((⊤ : G.Subgraph).deleteVerts (gallaiD G)ᶜ).coe

/-- The subgraph induced by the Gallai–Edmonds set `C`. -/
def gallaiGraphC [Finite V] (G : SimpleGraph V) :
    SimpleGraph ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts) :=
  ((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).coe

/-- Every vertex of `G[C]` lies in `C`. -/
theorem gallaiGraphC_mem_C [Finite V] (G : SimpleGraph V)
    (x : ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts)) :
    (x : V) ∈ gallaiC G := by
  have hx : (x : V) ∈ Set.univ \ (gallaiC G)ᶜ := x.2
  rw [Set.mem_sdiff] at hx
  exact not_not.mp hx.2

/-- Adjacency in `G[C]` is adjacency in `G`. -/
theorem gallaiGraphC_adj [Finite V] (G : SimpleGraph V)
    {a b : ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts)} :
    (gallaiGraphC G).Adj a b ↔ G.Adj (a : V) (b : V) := by
  constructor
  · intro h
    exact ((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).adj_sub h
  · intro h
    have ha : (a : V) ∈ Set.univ \ (gallaiC G)ᶜ := a.2
    have hb : (b : V) ∈ Set.univ \ (gallaiC G)ᶜ := b.2
    rw [Set.mem_sdiff] at ha hb
    change ((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).Adj _ _
    exact SimpleGraph.Subgraph.deleteVerts_adj.mpr
      ⟨by rw [SimpleGraph.Subgraph.verts_top]; trivial, ha.2,
        by rw [SimpleGraph.Subgraph.verts_top]; trivial, hb.2,
        SimpleGraph.Subgraph.top_adj.mpr h⟩

/-- The `D`-component containing `d ∈ D`. -/
def gallaiCompOf [Finite V] (G : SimpleGraph V) (d : V) (hd : d ∈ gallaiD G) :
    (gallaiGraphD G).ConnectedComponent :=
  (gallaiGraphD G).connectedComponentMk ⟨d, by
    show d ∈ ((⊤ : G.Subgraph).deleteVerts (gallaiD G)ᶜ).verts
    rw [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top]
    simpa using hd⟩

/-- The Gallai–Edmonds structural hypothesis (the *conclusion shape* of
Diestel Theorem 2.2.3 in the 5th edition — Theorem 2.3.1 in the 4th — as a
predicate): the components of `G[D]` are
factor-critical, `G[C]` has a perfect matching, and `A` is matched into
distinct components of `G[D]`.

Weakening note: this is deliberately weaker than the full theorem. Diestel
quantifies over *every maximum matching*; here the `A`-matching is an
arbitrary matching, not required to be maximum nor to extend the
component/`C` matchings. The unconditional proof (that every graph satisfies
this predicate in its full maximum-matching form) requires alternating-tree /
barrier machinery beyond this module (see the module docstring) and is left
as future work. The projections and counting corollaries below are the
machine-checked-correct conditional forms. -/
def IsGallaiEdmondsDecomp [Finite V] (G : SimpleGraph V) : Prop :=
  (∀ c : (gallaiGraphD G).ConnectedComponent,
    IsFactorCritical ((gallaiGraphD G).induce c.supp)) ∧
  (∃ M : (gallaiGraphC G).Subgraph, M.IsPerfectMatching) ∧
  ∃ M : G.Subgraph, M.IsMatching ∧
    (∀ a ∈ gallaiA G, ∃ d ∈ gallaiD G, M.Adj a d) ∧
    ∀ a₁ (_ha₁ : a₁ ∈ gallaiA G) a₂ (_ha₂ : a₂ ∈ gallaiA G)
      d₁ (hd₁ : d₁ ∈ gallaiD G) d₂ (hd₂ : d₂ ∈ gallaiD G),
      M.Adj a₁ d₁ → M.Adj a₂ d₂ →
        gallaiCompOf G d₁ hd₁ = gallaiCompOf G d₂ hd₂ → a₁ = a₂

/-- In a Gallai–Edmonds decomposition, each `D`-component is factor-critical. -/
theorem IsGallaiEdmondsDecomp.factorCritical_D [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) (c : (gallaiGraphD G).ConnectedComponent) :
    IsFactorCritical ((gallaiGraphD G).induce c.supp) :=
  h.1 c

/-- In a Gallai–Edmonds decomposition, `C` has a perfect matching. -/
theorem IsGallaiEdmondsDecomp.perfectMatching_C [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) :
    ∃ M : (gallaiGraphC G).Subgraph, M.IsPerfectMatching :=
  h.2.1

/-- In a Gallai–Edmonds decomposition, `A` is matched into `D`. -/
theorem IsGallaiEdmondsDecomp.matchable_A [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      ∀ a ∈ gallaiA G, ∃ d ∈ gallaiD G, M.Adj a d := by
  obtain ⟨M, hM, hA, -⟩ := h.2.2
  exact ⟨M, hM, hA⟩

/-- In a Gallai–Edmonds decomposition, `A` is matched into *distinct*
`D`-components. -/
theorem IsGallaiEdmondsDecomp.matchable_A_distinct [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      (∀ a ∈ gallaiA G, ∃ d ∈ gallaiD G, M.Adj a d) ∧
      ∀ a₁ (_ha₁ : a₁ ∈ gallaiA G) a₂ (_ha₂ : a₂ ∈ gallaiA G)
        d₁ (hd₁ : d₁ ∈ gallaiD G) d₂ (hd₂ : d₂ ∈ gallaiD G),
        M.Adj a₁ d₁ → M.Adj a₂ d₂ →
          gallaiCompOf G d₁ hd₁ = gallaiCompOf G d₂ hd₂ → a₁ = a₂ :=
  h.2.2

/-- In a Gallai–Edmonds decomposition, every `D`-component is odd. -/
theorem IsGallaiEdmondsDecomp.odd_component [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) (c : (gallaiGraphD G).ConnectedComponent) :
    Odd (Nat.card ↥c.supp) := by
  have hfc := h.factorCritical_D c
  have : Finite ↥c.supp := inferInstance
  obtain ⟨x, hx⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
  have : Nonempty ↥c.supp := ⟨⟨x, hx⟩⟩
  exact hfc.odd_card

/-- In a Gallai–Edmonds decomposition, `G[C]` has even order. -/
theorem IsGallaiEdmondsDecomp.even_C [Finite V] {G : SimpleGraph V}
    (h : IsGallaiEdmondsDecomp G) :
    Even (Nat.card ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts)) := by
  have : Finite ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts) :=
    inferInstance
  have := Fintype.ofFinite ↥(((⊤ : G.Subgraph).deleteVerts (gallaiC G)ᶜ).verts)
  obtain ⟨M, hM⟩ := h.perfectMatching_C
  have heven := hM.even_card
  rw [Nat.card_eq_fintype_card]
  exact heven

end MathlibExt.Combinatorics.Matching.GallaiEdmonds
