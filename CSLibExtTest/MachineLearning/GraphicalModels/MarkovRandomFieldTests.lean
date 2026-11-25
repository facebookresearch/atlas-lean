/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovRandomField

/-!
# Tests for Markov random fields

Boundary checks on the `2 × 2` grid graph: its adjacency and cliques, separation
of the diagonal corners by the off-diagonal pair, the constant Gibbs weight, and
the resulting conditional independence of the diagonal corners.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.MarkovRandomFieldTest

open MetaMathlibExt.FiniteWeight Cslib.MachineLearning.GraphicalModels

/-- The `2 × 2` grid graph on `Fin 2 × Fin 2`: horizontal and vertical neighbors. -/
def gridGraph : SimpleGraph (Fin 2 × Fin 2) :=
  SimpleGraph.fromRel (fun a b =>
    (a.1 = b.1 ∧ a.2.val + 1 = b.2.val) ∨ (a.2 = b.2 ∧ a.1.val + 1 = b.1.val))

theorem grid_not_adj_diagonal : ¬ gridGraph.Adj (0, 0) (1, 1) := by
  simp only [gridGraph, SimpleGraph.fromRel]
  decide

theorem grid_adj_horizontal : gridGraph.Adj (0, 0) (0, 1) := by
  simp only [gridGraph, SimpleGraph.fromRel]
  decide

theorem grid_isClique_edge : gridGraph.IsClique ({(0, 0), (0, 1)} : Set (Fin 2 × Fin 2)) := by
  intro x hx y hy hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hne
  · exact grid_adj_horizontal
  · simp only [gridGraph, SimpleGraph.fromRel]
    decide
  · exact absurd rfl hne

theorem grid_not_isClique_diagonal :
    ¬ gridGraph.IsClique ({(0, 0), (1, 1)} : Set (Fin 2 × Fin 2)) := by
  intro h
  have mem1 : (0, 0) ∈ ({(0, 0), (1, 1)} : Set (Fin 2 × Fin 2)) := by simp
  have mem2 : (1, 1) ∈ ({(0, 0), (1, 1)} : Set (Fin 2 × Fin 2)) := by simp
  have hne : ((0, 0) : Fin 2 × Fin 2) ≠ (1, 1) := by decide
  exact grid_not_adj_diagonal (h mem1 mem2 hne)

/-- The two off-diagonal corners separate the diagonal corners in the `2 × 2` grid. -/
theorem grid_separatedBy :
    gridGraph.SeparatedBy {(0, 0)} {(1, 1)} {(0, 1), (1, 0)} := by
  have hstart : ∀ {u b : Fin 2 × Fin 2} (w' : gridGraph.Walk u b), u ∈ w'.support := by
    intro u b w'
    cases w' with
    | nil => simp [SimpleGraph.Walk.support_nil]
    | cons h tail => simp [SimpleGraph.Walk.support_cons]
  have hnb : ∀ u : Fin 2 × Fin 2, gridGraph.Adj (0, 0) u → u = (0, 1) ∨ u = (1, 0) := by
    intro u hu
    have h4 : ∀ v : Fin 2 × Fin 2,
        v = (0, 0) ∨ v = (0, 1) ∨ v = (1, 0) ∨ v = (1, 1) := by
      decide
    rcases h4 u with rfl | rfl | rfl | rfl
    · exact absurd rfl (gridGraph.ne_of_adj hu)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hu grid_not_adj_diagonal
  intro a b ha hb w
  simp only [Set.mem_singleton_iff] at ha hb
  cases w with
  | nil =>
    subst ha
    exact absurd hb (by decide)
  | cons hadj w' =>
    subst ha
    subst hb
    rcases hnb _ hadj with rfl | rfl
    · refine ⟨(0, 1), by simp, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (hstart w')
    · refine ⟨(1, 0), by simp, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (hstart w')

/-- The constant weight `1` Gibbs-factorizes over the grid (empty potential family
after normalization: use any family of cliques with all potentials `1`). -/
theorem grid_gibbsFactorization_one :
    GibbsFactorization gridGraph (fun _ : Fin 2 × Fin 2 → Bool => 1) := by
  refine ⟨∅, fun _ _ => 1, by simp, by simp, by simp, by simp⟩

/-- On the grid, every Gibbs weight makes the diagonal corners conditionally
independent given the off-diagonal corners. -/
theorem grid_condIndep_of_gibbsFactorization {p : (Fin 2 × Fin 2 → Bool) → ℝ}
    (h : GibbsFactorization gridGraph p) :
    CondIndep p {(0, 0)} {(1, 1)} {(0, 1), (1, 0)} := by
  exact (globalMarkov_of_gibbsFactorization h) _ _ _ grid_separatedBy

end Cslib.MachineLearning.GraphicalModels.MarkovRandomFieldTest
