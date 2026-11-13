/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace SimpleGraph

/-- **Dominating set.** A set $S$ of vertices of a simple graph $G$ dominates $G$ when every vertex
of $G$ lies in $S$ or is adjacent to some vertex of $S$. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v

/-- **Independent dominating set.** A set $S$ of vertices of a simple graph $G$ is an independent
dominating set of $G$ when no two vertices of $S$ are adjacent and $S$ dominates $G$. -/
def IsIndepDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsIndepSet S ∧ G.IsDominating S

/-- **Domination number.** For a simple graph $G$ on a finite vertex set, the domination number of
$G$ is the least number of elements of a dominating set of $G$. -/
noncomputable def dominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}

/-- **Independent domination number.** For a simple graph $G$ on a finite vertex set, the
independent domination number of $G$ is the least number of elements of an independent dominating
set of $G$. -/
noncomputable def indepDominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}

/-- Every finite graph has an independent dominating set. -/
theorem exists_isIndepDominating {V : Type*} (G : SimpleGraph V) [Finite V] :
    ∃ S : Finset V, G.IsIndepDominating ↑S := by
  classical
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  refine ⟨S, hS.isIndepSet, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · exact Or.inl (by simpa using hv)
  · right
    by_contra h
    have h' : ∀ u ∈ (↑S : Set V), ¬ G.Adj u v := by
      intro u hu hadj
      exact h ⟨u, hu, hadj⟩
    have h_indep : G.IsIndepSet (insert v (↑S : Set V)) := by
      rw [isIndepSet_iff]
      intro x hx y hy hxy hadj
      rw [Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact hxy rfl
        · exact h' y hy hadj.symm
      · rcases hy with rfl | hy
        · exact h' x hx hadj
        · exact hS.isIndepSet hx hy hxy hadj
    have hsub : insert v (↑S : Set V) ⊆ (↑S : Set V) :=
      (hS.isMaximalIndepSet S).2 h_indep (Set.subset_insert v ↑S)
    exact hv (by simpa using hsub (Set.mem_insert v ↑S))

/-- **A minimum independent dominating set exists.** Every simple graph $G$ on a finite vertex set
has an independent dominating set whose number of elements equals the independent domination
number of $G$. -/
theorem exists_indepDominationNumber_eq_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] :
    ∃ S : Finset V, S.card = G.indepDominationNumber ∧ G.IsIndepDominating ↑S := by
  classical
  unfold indepDominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}.Nonempty := by
    obtain ⟨S, hS⟩ := G.exists_isIndepDominating
    exact ⟨S.card, S, rfl, hS⟩
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

/-- **Independent dominating sets are at least as large as the independent domination number.**
Let $G$ be a simple graph on a finite vertex set. If $S$ is an independent dominating set of $G$,
then the independent domination number of $G$ is at most the number of elements of $S$. -/
theorem indepDominationNumber_le_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] {S : Finset V} (hS : G.IsIndepDominating ↑S) :
    G.indepDominationNumber ≤ S.card := by
  unfold indepDominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

/-- **A minimum dominating set exists.** Every simple graph $G$ on a finite vertex set has a
dominating set whose number of elements equals the domination number of $G$. -/
theorem exists_dominationNumber_eq_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] :
    ∃ S : Finset V, S.card = G.dominationNumber ∧ G.IsDominating ↑S := by
  classical
  unfold dominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}.Nonempty := by
    refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
    intro v
    exact Or.inl (by simp)
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

/-- **Dominating sets are at least as large as the domination number.** Let $G$ be a simple graph
on a finite vertex set. If $S$ is a dominating set of $G$, then the domination number of $G$ is at
most the number of elements of $S$. -/
theorem dominationNumber_le_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] {S : Finset V} (hS : G.IsDominating ↑S) :
    G.dominationNumber ≤ S.card := by
  unfold dominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

end SimpleGraph
