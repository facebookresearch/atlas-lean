/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.ErdosProblem1034

@[expose] public section

namespace MathlibExt.GraphTheory.ErdosProblem1034Wanted

example : ¬ conjecture := conjecture_refuted

example : disprovedForm := conjecture_refuted

/-! ### `JoinedToTwo` -/

/-- The empty set is joined to two vertices of any set. -/
example {V : Type*} (G : SimpleGraph V) (T : Finset V) : JoinedToTwo G T ∅ := by
  simp [JoinedToTwo]

/-- Every vertex of a triangle is adjacent to its two other vertices. -/
example : JoinedToTwo (⊤ : SimpleGraph (Fin 3)) Finset.univ Finset.univ := by
  unfold JoinedToTwo
  decide

/-- In a graph without edges, no vertex is joined to two vertices of a set. -/
example : ¬ JoinedToTwo (⊥ : SimpleGraph (Fin 3)) Finset.univ {0} := by
  unfold JoinedToTwo
  decide

/-! ### The counterexample graphs -/

/-- `CliqueJoin.graph 2 2 3` is the join of an independent set of two vertices with two disjoint
triangles. -/
example : ∀ a b : Fin 2 ⊕ (Fin 2 × Fin 3), (CliqueJoin.graph 2 2 3).Adj a b ↔
    (a.isLeft ∧ b.isRight) ∨ (a.isRight ∧ b.isLeft) ∨
      ∃ x y : Fin 2 × Fin 3, a = .inr x ∧ b = .inr y ∧ x.1 = y.1 ∧ x ≠ y := by
  decide

/-- The edge count, computed directly, agrees with `CliqueJoin.two_mul_card_edgeFinset`. -/
example : (CliqueJoin.graph 2 2 3).edgeFinset.card = 18 := by decide

example : 2 * (CliqueJoin.graph 2 2 3).edgeFinset.card = 36 :=
  CliqueJoin.two_mul_card_edgeFinset

/-- With cliques of one vertex, `CliqueJoin.graph p k 1` is the complete bipartite graph
`K_{p,k}`. -/
example : (CliqueJoin.graph 3 2 1).edgeFinset.card = 6 := by decide

example (p k : ℕ) : 2 * (CliqueJoin.graph p k 1).edgeFinset.card = 2 * (p * k) := by
  rw [CliqueJoin.two_mul_card_edgeFinset]
  ring

/-- Without clique vertices there are no edges. -/
example (p k : ℕ) : (CliqueJoin.graph p k 0).edgeFinset.card = 0 := by
  have h := CliqueJoin.two_mul_card_edgeFinset (p := p) (k := k) (q := 0)
  simpa using h

/-- The degrees in `CliqueJoin.graph 2 2 3`. -/
example : (CliqueJoin.graph 2 2 3).degree (.inl 0) = 6 ∧
    (CliqueJoin.graph 2 2 3).degree (.inr (1, 2)) = 4 :=
  ⟨CliqueJoin.degree_inl 0, CliqueJoin.degree_inr (1, 2)⟩

/-- `CliqueJoin.block 2 3 0` consists of the independent set and the first triangle. -/
example : CliqueJoin.block 2 3 (0 : Fin 2) =
    {.inl 0, .inl 1, .inr (0, 0), .inr (0, 1), .inr (0, 2)} := by
  decide

/-! ### Triangles and the bound `p + q` -/

/-- A triangle with a vertex in the independent set: the whole of `CliqueJoin.block 2 3 0`
is joined to two of its vertices, so the bound `p + q` of
`CliqueJoin.card_le_of_joinedToTwo` is attained. -/
example : (CliqueJoin.graph 2 2 3).IsNClique 3 {.inl 0, .inr (0, 0), .inr (0, 1)} ∧
    JoinedToTwo (CliqueJoin.graph 2 2 3) {.inl 0, .inr (0, 0), .inr (0, 1)}
      (CliqueJoin.block 2 3 0) ∧
    (CliqueJoin.block 2 3 (0 : Fin 2)).card = 2 + 3 := by
  unfold JoinedToTwo
  decide

/-- A triangle inside a clique: the bound is attained as well. -/
example : (CliqueJoin.graph 2 2 3).IsNClique 3 {.inr (0, 0), .inr (0, 1), .inr (0, 2)} ∧
    JoinedToTwo (CliqueJoin.graph 2 2 3) {.inr (0, 0), .inr (0, 1), .inr (0, 2)}
      (CliqueJoin.block 2 3 0) := by
  unfold JoinedToTwo
  decide

/-- A vertex of another clique is adjacent to at most one vertex of the triangle. -/
example : ¬ JoinedToTwo (CliqueJoin.graph 2 2 3) {.inl 0, .inr (0, 0), .inr (0, 1)}
    {.inr (1, 0)} := by
  unfold JoinedToTwo
  decide

/-- The independent set contains no triangle. -/
example : ¬ (CliqueJoin.graph 2 2 3).IsNClique 3 {.inl 0, .inl 1, .inr (0, 0)} := by decide

/-- `CliqueJoin.card_le_of_joinedToTwo` for the graph itself, pulled back along the identity. -/
example {p k q : ℕ} {T Y : Finset (Fin p ⊕ (Fin k × Fin q))}
    (hT : (CliqueJoin.graph p k q).IsNClique 3 T) (hY : JoinedToTwo (CliqueJoin.graph p k q) T Y) :
    Y.card ≤ p + q :=
  CliqueJoin.card_le_of_joinedToTwo (c := id) Function.injective_id hT hY

end MathlibExt.GraphTheory.ErdosProblem1034Wanted
