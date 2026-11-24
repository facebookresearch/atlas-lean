/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Tactic.FinCases

namespace MetaMathlibExt

@[expose] public section

/-! ## The Make-A-Cycle and Avoid-A-Cycle games

The completed game API for Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis,
and Minh Phan, *Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4: the game
predicates, their recurrences, graph joins, and the generalized Petersen graph with
its adjacency lemmas. The deferred game-result statements using this API are in
`WantedExt.Combinatorics.SimpleGraph.CycleGamesOnGraphsWanted`. -/

section Games

variable {V : Type*} [DecidableEq V]

/-- Whether the player to move wins the Make-A-Cycle game `MAC(G, v)` from the position with
visited vertex set `S`, previous vertex `p` (`none` before the first move) and current vertex
`c`. A move goes along an edge `c w` other than the edge just used (`w ≠ p`); moving to an
already visited vertex wins at once, and a player with no legal move loses. The game
`MAC(G, v)` itself is the position `makeACycleWins G {v} none v`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
def makeACycleWins [Fintype V] (G : SimpleGraph V) (S : Finset V) (p : Option V) (c : V) : Prop :=
  ∃ w, G.Adj c w ∧ p ≠ some w ∧
    if _h : w ∈ S then True else ¬ makeACycleWins G (insert w S) (some c) w
termination_by Fintype.card V - S.card
decreasing_by
  have h1 := Finset.card_insert_of_notMem _h
  have h2 := Finset.card_le_univ (insert w S)
  omega

/-- Whether the player to move wins the Avoid-A-Cycle game `AAC(G, v)` (the misère version of
Make-A-Cycle) from the position with visited vertex set `S`, previous vertex `p` and current
vertex `c`: moving to an already visited vertex loses at once, and a player with no legal move
loses. The game `AAC(G, v)` itself is the position `avoidACycleWins G {v} none v`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
def avoidACycleWins [Fintype V] (G : SimpleGraph V) (S : Finset V) (p : Option V) (c : V) : Prop :=
  ∃ w, G.Adj c w ∧ p ≠ some w ∧
    if _h : w ∈ S then False else ¬ avoidACycleWins G (insert w S) (some c) w
termination_by Fintype.card V - S.card
decreasing_by
  have h1 := Finset.card_insert_of_notMem _h
  have h2 := Finset.card_le_univ (insert w S)
  omega

/-- One-step recurrence for `makeACycleWins`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
theorem makeACycleWins_iff [Fintype V] (G : SimpleGraph V) (S : Finset V) (p : Option V) (c : V) :
    makeACycleWins G S p c ↔ ∃ w, G.Adj c w ∧ p ≠ some w ∧
      (w ∈ S ∨ (w ∉ S ∧ ¬ makeACycleWins G (insert w S) (some c) w)) := by
  rw [makeACycleWins]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases h : w ∈ S <;> simp [h]

/-- One-step recurrence for `avoidACycleWins`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
theorem avoidACycleWins_iff [Fintype V] (G : SimpleGraph V) (S : Finset V) (p : Option V) (c : V) :
    avoidACycleWins G S p c ↔ ∃ w, G.Adj c w ∧ p ≠ some w ∧ w ∉ S ∧
      ¬ avoidACycleWins G (insert w S) (some c) w := by
  rw [avoidACycleWins]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases h : w ∈ S <;> simp [h]

/-- A player whose current vertex has no neighbours has no legal move and loses
Make-A-Cycle.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
theorem not_makeACycleWins_of_forall_not_adj [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (p : Option V) (c : V) (hc : ∀ w, ¬ G.Adj c w) : ¬ makeACycleWins G S p c := by
  rw [makeACycleWins_iff]
  rintro ⟨w, hw, -⟩
  exact hc w hw

/-- A player whose current vertex has no neighbours has no legal move and loses
Avoid-A-Cycle.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1. -/
theorem not_avoidACycleWins_of_forall_not_adj [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (p : Option V) (c : V) (hc : ∀ w, ¬ G.Adj c w) : ¬ avoidACycleWins G S p c := by
  rw [avoidACycleWins_iff]
  rintro ⟨w, hw, -⟩
  exact hc w hw

end Games

/-- On the single edge `K₂`, Player 1 wins Make-A-Cycle: after the first move Player 2 cannot
backtrack along the same edge and has no legal move.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1 and Theorem 3.1 (case
`n = 2`). -/
theorem makeACycleWins_completeGraph_two :
    makeACycleWins (⊤ : SimpleGraph (Fin 2)) {0} none 0 := by
  rw [makeACycleWins_iff]
  refine ⟨1, by simp, by simp, Or.inr ⟨by simp, ?_⟩⟩
  rw [makeACycleWins_iff]
  rintro ⟨w, hw, hp, -⟩
  fin_cases w
  · simp at hp
  · simp at hw

/-- On the single edge `K₂`, Player 1 wins Avoid-A-Cycle.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 2.1 and Theorem 3.1 (case
`n = 2`). -/
theorem avoidACycleWins_completeGraph_two :
    avoidACycleWins (⊤ : SimpleGraph (Fin 2)) {0} none 0 := by
  rw [avoidACycleWins_iff]
  refine ⟨1, by simp, by simp, by simp, ?_⟩
  rw [avoidACycleWins_iff]
  rintro ⟨w, hw, hp, -⟩
  fin_cases w
  · simp at hp
  · simp at hw

/-! ## Graph constructions -/

/-- The graph join `G + H`: the disjoint union of `G` and `H` together with every edge between
a vertex of `G` and a vertex of `H`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6.2. -/
def graphJoin {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (G ⊕g H) ⊔ completeBipartiteGraph V W

/-- Inside the left summand the join has the edges of `G`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6.2. -/
@[simp] theorem graphJoin_adj_inl_inl {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (a b : V) : (graphJoin G H).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
  simp [graphJoin]

/-- Inside the right summand the join has the edges of `H`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6.2. -/
@[simp] theorem graphJoin_adj_inr_inr {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (a b : W) : (graphJoin G H).Adj (Sum.inr a) (Sum.inr b) ↔ H.Adj a b := by
  simp [graphJoin]

/-- Every vertex of `G` is adjacent in the join to every vertex of `H`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6.2. -/
@[simp] theorem graphJoin_adj_inl_inr {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (a : V) (b : W) : (graphJoin G H).Adj (Sum.inl a) (Sum.inr b) := by
  simp [graphJoin]

/-- The straight join `G ↔ H` of two graphs on the same vertex set: the disjoint union of `G`
and `H` together with the edges joining the two copies `inl a` and `inr a` of each vertex `a`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 6.7. -/
def straightJoin {V : Type*} (G H : SimpleGraph V) : SimpleGraph (V ⊕ V) :=
  (G ⊕g H) ⊔ SimpleGraph.fromRel fun x y => ∃ a, x = Sum.inl a ∧ y = Sum.inr a

/-- Inside the left summand the straight join has the edges of `G`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 6.7. -/
@[simp] theorem straightJoin_adj_inl_inl {V : Type*} (G H : SimpleGraph V) (a b : V) :
    (straightJoin G H).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
  simp [straightJoin]

/-- Inside the right summand the straight join has the edges of `H`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 6.7. -/
@[simp] theorem straightJoin_adj_inr_inr {V : Type*} (G H : SimpleGraph V) (a b : V) :
    (straightJoin G H).Adj (Sum.inr a) (Sum.inr b) ↔ H.Adj a b := by
  simp [straightJoin]

/-- A vertex of the left copy is adjacent to a vertex of the right copy exactly when they are
copies of the same vertex.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Definition 6.7. -/
@[simp] theorem straightJoin_adj_inl_inr {V : Type*} (G H : SimpleGraph V) (a b : V) :
    (straightJoin G H).Adj (Sum.inl a) (Sum.inr b) ↔ a = b := by
  simp [straightJoin, eq_comm]

/-- The generalized Petersen graph `GP(n, k)` on the `2n` vertices `uᵢ = (false, i)` and
`vᵢ = (true, i)`, `i : Fin n`, with edges `uᵢ uᵢ₊₁`, `uᵢ vᵢ` and `vᵢ vᵢ₊ₖ`, indices taken
modulo `n`. The paper uses it for `2 ≤ 2k ≤ n`, `n ≥ 3`, including `2k = n`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
def generalizedPetersenGraph (n k : ℕ) : SimpleGraph (Bool × Fin n) :=
  SimpleGraph.fromRel fun x y =>
    (x.1 = false ∧ y.1 = false ∧ (x.2.val + 1) % n = y.2.val) ∨
      (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
      (x.1 = true ∧ y.1 = true ∧ (x.2.val + k) % n = y.2.val)

/-- The spoke `uᵢ vᵢ` is an edge of `GP(n, k)`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
theorem generalizedPetersenGraph_adj_spoke (n k : ℕ) (i : Fin n) :
    (generalizedPetersenGraph n k).Adj (false, i) (true, i) := by
  simp [generalizedPetersenGraph]

/-- Two outer vertices `uᵢ`, `uⱼ` of `GP(n, k)` are adjacent exactly when they are distinct
and consecutive modulo `n`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
theorem generalizedPetersenGraph_adj_outer (n k : ℕ) (i j : Fin n) :
    (generalizedPetersenGraph n k).Adj (false, i) (false, j) ↔
      i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) := by
  simp [generalizedPetersenGraph]

/-- Two inner vertices `vᵢ`, `vⱼ` of `GP(n, k)` are adjacent exactly when they are distinct
and differ by `k` modulo `n`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
@[simp] theorem generalizedPetersenGraph_adj_inner (n k : ℕ) (i j : Fin n) :
    (generalizedPetersenGraph n k).Adj (true, i) (true, j) ↔
      i ≠ j ∧ ((i.val + k) % n = j.val ∨ (j.val + k) % n = i.val) := by
  simp [generalizedPetersenGraph]

/-- An outer vertex `uᵢ` and an inner vertex `vⱼ` of `GP(n, k)` are adjacent exactly when
`i = j` (the spoke `uᵢ vᵢ`).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
@[simp] theorem generalizedPetersenGraph_adj_outer_inner (n k : ℕ) (i j : Fin n) :
    (generalizedPetersenGraph n k).Adj (false, i) (true, j) ↔ i = j := by
  simp only [generalizedPetersenGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩ <;> simp_all
  · rintro rfl; simp

/-- An inner vertex `vᵢ` and an outer vertex `uⱼ` of `GP(n, k)` are adjacent exactly when
`i = j` (the spoke `uᵢ vᵢ`).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Section 6. -/
@[simp] theorem generalizedPetersenGraph_adj_inner_outer (n k : ℕ) (i j : Fin n) :
    (generalizedPetersenGraph n k).Adj (true, i) (false, j) ↔ i = j := by
  simp only [generalizedPetersenGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩ <;> simp_all [eq_comm]
  · rintro rfl; simp

end

end MetaMathlibExt
