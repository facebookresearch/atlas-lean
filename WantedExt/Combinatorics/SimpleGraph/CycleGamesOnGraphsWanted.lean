/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import MathlibExt.Combinatorics.Matching.GallaiEdmonds
public import MathlibExt.Combinatorics.SimpleGraph.VertexTransitive

namespace MetaMathlibExt

@[expose] public section

/-! ## The Make-A-Cycle and Avoid-A-Cycle games -/

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


/-- A connected vertex-transitive finite graph has a perfect matching when its order
is even, and, when its order is odd, for every vertex `v` a near-perfect matching
leaving exactly `v` unsaturated. Vertex-transitivity is `SimpleGraph.IsVertexTransitive`;
the odd case is factor-criticality (`GallaiEdmonds.IsFactorCritical`: for every `v`,
the graph induced on the other vertices has a perfect matching).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 2.9
(`integers-2024-G4-thm-2-9`). -/
public theorem_wanted connected_vertexTransitive_exists_matching {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (ht : G.IsVertexTransitive) :
    (Even (Fintype.card V) → ∃ M : G.Subgraph, M.IsPerfectMatching) ∧
      (Odd (Fintype.card V) →
        MathlibExt.Combinatorics.Matching.GallaiEdmonds.IsFactorCritical G)

/-! ## Game results -/

/-- Graph automorphisms preserve the outcome of both games: if `w` lies in the orbit of `v`
under `Aut(G)`, Player 1 wins `MAC(G, v)` iff Player 1 wins `MAC(G, w)`, and likewise for
`AAC`. The paper states an isomorphism of games (identical game trees); this records the
outcome consequence only.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 2.3
(`integers-2024-G4-thm-2-3`). -/
public theorem_wanted cycleGames_outcome_eq_of_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (φ : G ≃g G) (v : V) :
    (makeACycleWins G {v} none v ↔ makeACycleWins G {φ v} none (φ v)) ∧
      (avoidACycleWins G {v} none v ↔ avoidACycleWins G {φ v} none (φ v))

/-- On a vertex-transitive finite graph the outcomes of `MAC(G, v)` and of `AAC(G, v)` do not
depend on the starting vertex. The paper states an isomorphism of games; this records the
outcome consequence only.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Corollary 2.4
(`integers-2024-G4-cor-2-4`). -/
public theorem_wanted cycleGames_outcome_eq_of_isVertexTransitive {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (hG : G.IsVertexTransitive) (v w : V) :
    (makeACycleWins G {v} none v ↔ makeACycleWins G {w} none w) ∧
      (avoidACycleWins G {v} none v ↔ avoidACycleWins G {w} none w)

/-- Player 1 wins `AAC(G, v)` on a finite simple graph iff every maximum matching of `G`
saturates `v` (the undirected vertex geography theorem of Fraenkel, Scheinerman and Ullman,
quoted as Theorem 1.1 of the paper's reference [5]).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 2.8
(`integers-2024-G4-thm-2-8`). -/
public theorem_wanted avoidACycleWins_iff_forall_isMaximumMatching {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (v : V) :
    avoidACycleWins G {v} none v ↔
      ∀ M : G.Subgraph,
        MathlibExt.Combinatorics.Matching.IsMaximumMatching G M → v ∈ M.verts

/-- For a finite group `Γ` with generating set `S`, Player 1 wins the Relator Avoidance game
`RAV(Γ, S)` iff `|Γ|` is even. `RAV(Γ, S)` is read, as the paper identifies it in Section 2, as
`AAC` on the Cayley graph `SimpleGraph.mulCayley S` started at the identity.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Corollary 2.10
(`integers-2024-G4-cor-2-10`). -/
public theorem_wanted avoidACycleWins_mulCayley_iff_even {Γ : Type*} [Group Γ] [Fintype Γ]
    [DecidableEq Γ] (S : Set Γ) (hS : Subgroup.closure S = ⊤) :
    avoidACycleWins (SimpleGraph.mulCayley S) {1} none 1 ↔ Even (Fintype.card Γ)

/-- On the complete graph `Kₙ` (`n ≥ 1`), Player 1 wins `MAC(Kₙ)` iff `n ≥ 2`, and Player 1
wins `AAC(Kₙ)` iff `n` is even.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 3.1
(`integers-2024-G4-thm-3-1`). -/
public theorem_wanted cycleGames_completeGraph (n : ℕ) (hn : 1 ≤ n) :
    (makeACycleWins (⊤ : SimpleGraph (Fin n)) {⟨0, hn⟩} none ⟨0, hn⟩ ↔ 2 ≤ n) ∧
      (avoidACycleWins (⊤ : SimpleGraph (Fin n)) {⟨0, hn⟩} none ⟨0, hn⟩ ↔ Even n)

/-- On a complete `k`-partite graph `K(n₁, …, nₖ)` (`k ≥ 2`, all parts nonempty), Player 2 wins
`MAC(Γ, v)` when the part of `v` has at least two vertices, and Player 1 wins when it has
exactly one. Parts are indexed by `Fin k`; the ordering `n₁ ≤ ⋯ ≤ nₖ` is not needed.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 3.2
(`integers-2024-G4-thm-3-2`). -/
public theorem_wanted makeACycleWins_completeMultipartite {k : ℕ} (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (v : Σ i, Fin (n i)) :
    makeACycleWins (SimpleGraph.completeMultipartiteGraph fun i => Fin (n i)) {v} none v ↔
      n v.1 = 1

/-- On a complete `k`-partite graph `K(n₁, …, nₖ)` with `1 ≤ n₁ ≤ ⋯ ≤ nₖ` and `n = ∑ nᵢ`:
if `nₖ ≤ n / 2`, Player 1 wins `AAC(Γ, v)` for every `v` iff `n` is even; if `nₖ > n / 2`,
Player 1 wins `AAC(Γ, v)` iff `v` is not in the last part. The extracted record prints the
threshold as `n₂`; the proof in the paper (`m = ⌊n/2⌋`, "more than half of the vertices lie in
`Vₖ`") fixes it as `n/2`, and the `n₂` reading fails for `K(1, 1, 2)`, where Player 1 wins
from the part of size 2. The threshold is stated as `2 nₖ ≤ n`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 3.3
(`integers-2024-G4-thm-3-3`). -/
public theorem_wanted avoidACycleWins_completeMultipartite {k : ℕ} (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (hmono : Monotone n) :
    (2 * n ⟨k - 1, by omega⟩ ≤ ∑ i, n i →
      ∀ v : Σ i, Fin (n i),
        avoidACycleWins (SimpleGraph.completeMultipartiteGraph fun i => Fin (n i)) {v} none v ↔
          Even (∑ i, n i)) ∧
    (∑ i, n i < 2 * n ⟨k - 1, by omega⟩ →
      ∀ v : Σ i, Fin (n i),
        avoidACycleWins (SimpleGraph.completeMultipartiteGraph fun i => Fin (n i)) {v} none v ↔
          v.1 ≠ ⟨k - 1, by omega⟩)

/-- Player 1 wins Make-A-Cycle on the wheel `Wₙ` (`n ≥ 4`) started at the centre `u`. The wheel
is the join `Cₙ₋₁ + K₁` (paper, Section 4), with the centre the vertex of `K₁`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 4.1
(`integers-2024-G4-thm-4-1`). -/
public theorem_wanted makeACycleWins_wheel_center (n : ℕ) (hn : 4 ≤ n) :
    makeACycleWins (graphJoin (SimpleGraph.cycleGraph (n - 1)) (⊤ : SimpleGraph Unit))
      {Sum.inr ()} none (Sum.inr ())

/-- On the wheel `Wₙ = Cₙ₋₁ + K₁` (`n ≥ 4`), Player 1 wins Make-A-Cycle started at the rim
vertex `v₀` iff `n` is even.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 4.2
(`integers-2024-G4-thm-4-2`). -/
public theorem_wanted makeACycleWins_wheel_rim (n : ℕ) (hn : 4 ≤ n) :
    makeACycleWins (graphJoin (SimpleGraph.cycleGraph (n - 1)) (⊤ : SimpleGraph Unit))
      {Sum.inl ⟨0, by omega⟩} none (Sum.inl ⟨0, by omega⟩) ↔ Even n

/-- On the wheel `Wₙ = Cₙ₋₁ + K₁` (`n ≥ 4`), Player 1 wins `AAC(Wₙ, v)` iff `n` is even, for
every starting vertex `v`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 4.3
(`integers-2024-G4-thm-4-3`). -/
public theorem_wanted avoidACycleWins_wheel (n : ℕ) (hn : 4 ≤ n)
    (v : Fin (n - 1) ⊕ Unit) :
    avoidACycleWins (graphJoin (SimpleGraph.cycleGraph (n - 1)) (⊤ : SimpleGraph Unit))
      {v} none v ↔ Even n

/-- For odd `n ≥ 3`, Player 1 wins Make-A-Cycle on the stacked prism `SP(n, 3) = Cₙ □ P₃` from
every starting vertex. Vertex `(i, j)` is position `i` on the `j`-th `n`-gon.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 5.2
(`integers-2024-G4-thm-5-2`). -/
public theorem_wanted makeACycleWins_stackedPrism_three_of_odd (n : ℕ) (hn : 3 ≤ n)
    (hodd : Odd n) (v : Fin n × Fin 3) :
    makeACycleWins (SimpleGraph.cycleGraph n □ SimpleGraph.pathGraph 3) {v} none v

/-- For even `n ≥ 4`, Player 2 wins Make-A-Cycle on `SP(n, 3) = Cₙ □ P₃` started at `(0, 0)` or
at `(0, 2)`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 5.4
(`integers-2024-G4-thm-5-4`). -/
public theorem_wanted not_makeACycleWins_stackedPrism_three_outer (n : ℕ) (hn : 4 ≤ n)
    (heven : Even n) (j : Fin 3) (hj : j = 0 ∨ j = 2) :
    ¬ makeACycleWins (SimpleGraph.cycleGraph n □ SimpleGraph.pathGraph 3)
      {(⟨0, by omega⟩, j)} none (⟨0, by omega⟩, j)

/-- In Make-A-Cycle on `SP(n, 3) = Cₙ □ P₃` with `n ≥ 4` even, started at `(0, 1)`: if
Player 1's first move is to `(1, 1)`, Player 2 (now to move) wins.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Lemma 5.6
(`integers-2024-G4-lem-5-6`). -/
public theorem_wanted makeACycleWins_stackedPrism_three_after_first_move (n : ℕ) (hn : 4 ≤ n)
    (heven : Even n) :
    makeACycleWins (SimpleGraph.cycleGraph n □ SimpleGraph.pathGraph 3)
      {(⟨0, by omega⟩, 1), (⟨1, by omega⟩, 1)} (some (⟨0, by omega⟩, 1)) (⟨1, by omega⟩, 1)

/-- For even `n ≥ 4`, Player 1 wins Make-A-Cycle on `SP(n, 3) = Cₙ □ P₃` started at `(0, 1)`
iff `n ≡ 2 (mod 8)` (Player 2 wins for `n ≡ 0, 4, 6 (mod 8)`).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 5.9
(`integers-2024-G4-thm-5-9`). -/
public theorem_wanted makeACycleWins_stackedPrism_three_middle (n : ℕ) (hn : 4 ≤ n)
    (heven : Even n) :
    makeACycleWins (SimpleGraph.cycleGraph n □ SimpleGraph.pathGraph 3)
      {(⟨0, by omega⟩, 1)} none (⟨0, by omega⟩, 1) ↔ n % 8 = 2

/-- On the stacked prism `SP(n, m) = Cₙ □ Pₘ` (`n ≥ 3`, `m ≥ 1`), Player 1 wins `AAC` from
every starting vertex iff `n` or `m` is even (Player 2 wins when both are odd).

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 5.10
(`integers-2024-G4-thm-5-10`). -/
public theorem_wanted avoidACycleWins_stackedPrism (n m : ℕ) (hn : 3 ≤ n) (hm : 1 ≤ m)
    (v : Fin n × Fin m) :
    avoidACycleWins (SimpleGraph.cycleGraph n □ SimpleGraph.pathGraph m) {v} none v ↔
      Even n ∨ Even m

/-- For `n ≥ 4` with `n ≢ 0 (mod 5)`, Player 1 wins Make-A-Cycle on `GP(n, 2)` started at `u₀`
and started at `v₀`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.2
(`integers-2024-G4-thm-6-2`). -/
public theorem_wanted makeACycleWins_generalizedPetersen_two (n : ℕ) (hn : 4 ≤ n)
    (h5 : n % 5 ≠ 0) :
    makeACycleWins (generalizedPetersenGraph n 2) {(false, ⟨0, by omega⟩)} none
        (false, ⟨0, by omega⟩) ∧
      makeACycleWins (generalizedPetersenGraph n 2) {(true, ⟨0, by omega⟩)} none
        (true, ⟨0, by omega⟩)

/-- For `n ≥ 4` with `n ≡ 0 (mod 5)`, Player 2 wins Make-A-Cycle on `GP(n, 2)` from every
starting vertex.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.6
(`integers-2024-G4-thm-6-6`). -/
public theorem_wanted not_makeACycleWins_generalizedPetersen_two (n : ℕ) (hn : 4 ≤ n)
    (h5 : n % 5 = 0) (v : Bool × Fin n) :
    ¬ makeACycleWins (generalizedPetersenGraph n 2) {v} none v

/-- On the straight join `Γ₁ ↔ Γ₂` of two finite graphs on the same vertex set, Player 1 wins
`AAC` from every starting vertex.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.8
(`integers-2024-G4-thm-6-8`). -/
public theorem_wanted avoidACycleWins_straightJoin {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (v : V ⊕ V) :
    avoidACycleWins (straightJoin G H) {v} none v

/-- On the generalized Petersen graph `GP(n, k)` (`n ≥ 3`, `2 ≤ 2k ≤ n`), Player 1 wins `AAC`
from every starting vertex.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Corollary 6.9
(`integers-2024-G4-cor-6-9`). -/
public theorem_wanted avoidACycleWins_generalizedPetersen (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hkn : 2 * k ≤ n) (v : Bool × Fin n) :
    avoidACycleWins (generalizedPetersenGraph n k) {v} none v

/-- On the join `Γ₁ + Γ₂` of two finite graphs with `2 ≤ |Γ₁| = |Γ₂|`, Player 1 wins `AAC` from
every starting vertex.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Corollary 6.10
(`integers-2024-G4-cor-6-10`). -/
public theorem_wanted avoidACycleWins_graphJoin_of_card_eq {V W : Type*} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (h2 : 2 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W) (v : V ⊕ W) :
    avoidACycleWins (graphJoin G H) {v} none v

/-- For finite graphs `Γ₁`, `Γ₂` with at least two vertices each and a start `sᵢ` in `Γᵢ`,
Player 1 wins `MAC(Γ₁ + Γ₂, sᵢ)` iff Player 1 wins `MAC(Γᵢ, sᵢ)` or `sᵢ` is adjacent to every
other vertex of `Γᵢ`. Both cases `i = 1` and `i = 2` are stated.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.11
(`integers-2024-G4-thm-6-11`). -/
public theorem_wanted makeACycleWins_graphJoin_iff {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (hV : 2 ≤ Fintype.card V) (hW : 2 ≤ Fintype.card W) :
    (∀ s : V, makeACycleWins (graphJoin G H) {Sum.inl s} none (Sum.inl s) ↔
      makeACycleWins G {s} none s ∨ ∀ w, w ≠ s → G.Adj s w) ∧
    (∀ s : W, makeACycleWins (graphJoin G H) {Sum.inr s} none (Sum.inr s) ↔
      makeACycleWins H {s} none s ∨ ∀ w, w ≠ s → H.Adj s w)

/-- For Cayley graphs `Γ₁ = Cay(G₁, S₁)` and `Γ₂ = Cay(G₂, S₂)` of finite groups with generating
sets, each with at least two vertices, and a start `s₁` in `Γ₁`, Player 1 wins
`AAC(Γ₁ + Γ₂, s₁)` iff `|Γ₁| ≡ |Γ₂| (mod 2)`. Cayley graphs are `SimpleGraph.mulCayley`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.12
(`integers-2024-G4-thm-6-12`). -/
public theorem_wanted avoidACycleWins_graphJoin_mulCayley_iff {G₁ G₂ : Type*} [Group G₁]
    [Group G₂] [Fintype G₁] [Fintype G₂] [DecidableEq G₁] [DecidableEq G₂] (S₁ : Set G₁)
    (S₂ : Set G₂) (hS₁ : Subgroup.closure S₁ = ⊤) (hS₂ : Subgroup.closure S₂ = ⊤)
    (h₁ : 2 ≤ Fintype.card G₁) (h₂ : 2 ≤ Fintype.card G₂) (s₁ : G₁) :
    avoidACycleWins (graphJoin (SimpleGraph.mulCayley S₁) (SimpleGraph.mulCayley S₂))
        {Sum.inl s₁} none (Sum.inl s₁) ↔
      Fintype.card G₁ % 2 = Fintype.card G₂ % 2

/-- On `GP(2n, n)` (`n ≥ 2`), Player 1 wins Make-A-Cycle started at `u₀` iff
`n ≢ 1, 3 (mod 6)`, and started at `v₀` iff `n ≢ 3 (mod 6)`.

Source: Zachary Gates, Drake Hayes, Robert Kelvey, Will Lillis, and Minh Phan,
*Cycle Games on Graphs*, INTEGERS 24 (2024), Article G4, Theorem 6.16
(`integers-2024-G4-thm-6-16`). -/
public theorem_wanted makeACycleWins_generalizedPetersen_double (n : ℕ) (hn : 2 ≤ n) :
    (makeACycleWins (generalizedPetersenGraph (2 * n) n) {(false, ⟨0, by omega⟩)} none
        (false, ⟨0, by omega⟩) ↔ n % 6 ≠ 1 ∧ n % 6 ≠ 3) ∧
      (makeACycleWins (generalizedPetersenGraph (2 * n) n) {(true, ⟨0, by omega⟩)} none
        (true, ⟨0, by omega⟩) ↔ n % 6 ≠ 3)

end

end MetaMathlibExt
