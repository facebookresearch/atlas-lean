/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

@[inherit_doc] scoped notation "α(" G ")" => indepNum G

@[simp] lemma indepNum_of_isEmpty [IsEmpty V] : α(G) = 0 := by
  simp [indepNum, isNIndepSet_iff, Subsingleton.elim _ ∅]

@[simp] lemma indepNum_pos [Finite V] [Nonempty V] : 0 < α(G) := by
  cases nonempty_fintype V
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← Nat.add_one_le_iff]
  exact le_csSup ⟨Nat.card V, by simp [mem_upperBounds, isNIndepSet_iff, Finset.card_le_univ]⟩
    ⟨{v}, by simp [isNIndepSet_iff]⟩

/-- The independence number is at most the number of vertices. -/
public theorem indepNum_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.indepNum ≤ Fintype.card V := by
  classical
  obtain ⟨s, hs⟩ := maximumIndepSet_exists (G := G)
  rw [← maximumIndepSet_card_eq_indepNum s hs]
  exact s.card_le_univ

/-- A nonedge witnesses independence number at least two. -/
public theorem two_le_indepNum_of_nonedge {V : Type*} [Finite V] {G : SimpleGraph V}
    {u v : V} (hne : u ≠ v) (h : ¬ G.Adj u v) : 2 ≤ G.indepNum := by
  classical
  have := Fintype.ofFinite V
  have hset : G.IsIndepSet (↑({u, v} : Finset V) : Set V) := by
    rw [isIndepSet_iff]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h
    · exact fun h' => h h'.symm
    · exact absurd rfl hxy
  have hle := hset.card_le_indepNum
  rwa [Finset.card_pair hne] at hle

/-- Infinite graphs: definitions for clique number so that the clique number of a graph
with unbounded clique size is `∞` rather than 0.
-/
noncomputable
def ecliqueNum (G : SimpleGraph V) : ℕ∞ := ⨆ (s : Finset V) (_ : G.IsClique s), #s

/-- The set of sizes of the inclusion-maximal finite cliques of `G` among finite
cliques. An infinite maximal clique is not represented. -/
def maximalCliqueSizes (G : SimpleGraph V) : Set ℕ :=
  { k | ∃ S : Finset V, Maximal (fun T : Finset V => G.IsClique (T : Set V)) S ∧ S.card = k }

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : G.edgeSet) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.1.toFinset ⊆ t)


end SimpleGraph
