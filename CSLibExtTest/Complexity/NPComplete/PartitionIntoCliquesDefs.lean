/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques

open MetaMathlibExt.BitstringEncoding

/-- Adjacency in the graph of an instance: distinct vertices with the edge listed in either
direction. -/
private theorem graph_adj (i : PartitionIntoCliquesInstance) (u v : Fin i.1) :
    (Graph i).Adj u v ↔ u ≠ v ∧ (((u : ℕ), (v : ℕ)) ∈ i.2.1 ∨ ((v : ℕ), (u : ℕ)) ∈ i.2.1) := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-! ### The graph of an instance -/

/-- An edge is symmetric: `(0, 1)` makes `1` adjacent to `0`. -/
example : (Graph ((2, [(0, 1)], 1) : PartitionIntoCliquesInstance)).Adj 1 0 :=
  (graph_adj _ 1 0).2 ⟨by decide, by decide⟩

/-- A listed loop gives no adjacency. -/
example : ¬ (Graph ((1, [(0, 0)], 1) : PartitionIntoCliquesInstance)).Adj 0 0 :=
  (Graph _).irrefl

/-- An edge with an endpoint outside the vertices gives no adjacency: the graph of
`(2, [(0, 5)], 1)` is empty. -/
example : Graph ((2, [(0, 5)], 1) : PartitionIntoCliquesInstance) = ⊥ := by
  ext u v
  rw [graph_adj]
  fin_cases u <;> fin_cases v <;> decide

/-- Unlisted pairs are not adjacent: the ends of the path `0 - 1 - 2` are not. -/
private theorem path_ends_not_adj (K : ℕ) :
    ¬ (Graph ((3, [(0, 1), (1, 2)], K) : PartitionIntoCliquesInstance)).Adj 0 2 := by
  simp [graph_adj]

/-! ### The triangle: one clique -/

/-- The triangle on the vertices `0`, `1`, `2` with the bound `K`. -/
private abbrev triangle (K : ℕ) : PartitionIntoCliquesInstance :=
  (3, [(0, 1), (1, 2), (0, 2)], K)

/-- The triangle with the bound `1` is well formed. -/
private theorem triangle_wellFormed : WellFormed (triangle 1) := by unfold WellFormed; decide

/-- All three vertices of the triangle form one block, which is a clique. -/
private theorem triangle_feasible : PartitionIntoCliquesFeasible (triangle 1) := by
  refine ⟨1, le_rfl, fun _ => 0, fun _ u _ v _ huv => (graph_adj _ u v).2 ⟨huv, ?_⟩⟩
  fin_cases u <;> fin_cases v <;> simp_all

/-- The decision problem accepts the encoding of the triangle with the bound `1`. -/
example : partitionIntoCliquesDec (bitEncode (triangle 1)) = true := by
  simp [partitionIntoCliquesDec, triangle_wellFormed, triangle_feasible]

/-! ### The path: two cliques, not one -/

/-- The path `0 - 1 - 2` with the bound `K`. -/
private abbrev path (K : ℕ) : PartitionIntoCliquesInstance := (3, [(0, 1), (1, 2)], K)

/-- The blocks `{0, 1}` and `{2}`, given by `c` with values in `Fin k` for any `k ≥ 2`. -/
private def pathBlocks (k : ℕ) (hk : 2 ≤ k) : Fin 3 → Fin k := fun v =>
  if v = 2 then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- Each block of `pathBlocks` is a clique of the path. -/
private theorem pathBlocks_clique (K k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    (Graph (path K)).IsClique {v | pathBlocks k hk v = j} := by
  intro u hu v hv huv
  change pathBlocks k hk u = j at hu
  change pathBlocks k hk v = j at hv
  refine (graph_adj _ u v).2 ⟨huv, ?_⟩
  fin_cases u <;> fin_cases v <;> simp_all [pathBlocks, Fin.ext_iff]

/-- The path splits into two cliques. -/
private theorem path_two_feasible : PartitionIntoCliquesFeasible (path 2) :=
  ⟨2, le_rfl, pathBlocks 2 le_rfl, pathBlocks_clique 2 2 le_rfl⟩

/-- The path with the bound `1` is well formed: `1` is positive and at most the three
vertices, so only the clique condition can reject it. -/
private theorem path_one_wellFormed : WellFormed (path 1) := by unfold WellFormed; decide

private theorem path_two_wellFormed : WellFormed (path 2) := by unfold WellFormed; decide

/-- The path is not one clique: one block would hold its two ends, which are not adjacent.
No map sends its vertices into `Fin 0` either. -/
private theorem path_one_infeasible : ¬ PartitionIntoCliquesFeasible (path 1) := by
  rintro ⟨k, hk, c, hc⟩
  change k ≤ 1 at hk
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact (c 0).elim0
  · exact path_ends_not_adj 1
      (hc 0 (Subsingleton.elim (c 0) 0) (Subsingleton.elim (c 2) 0) (by decide))

/-- The decision problem accepts the path with the bound `2` and rejects it with the bound
`1`, both instances being well formed. -/
example :
    partitionIntoCliquesDec (bitEncode (path 2)) = true ∧
      partitionIntoCliquesDec (bitEncode (path 1)) = false := by
  simp [partitionIntoCliquesDec, path_two_wellFormed, path_two_feasible, path_one_infeasible]

/-- `pathBlocks 3` leaves the block `2` empty. -/
private theorem pathBlocks_not_surjective : ¬ Function.Surjective (pathBlocks 3 (by decide)) :=
  fun h => by
    obtain ⟨v, hv⟩ := h 2
    fin_cases v <;> simp [pathBlocks, Fin.ext_iff] at hv

/-- Empty blocks are allowed: with the bound `3`, the path is feasible through the three
blocks `{0, 1}`, `{2}` and an empty one, given by a map that is not surjective. -/
example :
    PartitionIntoCliquesFeasible (path 3) ∧ ¬ Function.Surjective (pathBlocks 3 (by decide)) :=
  ⟨⟨3, le_rfl, pathBlocks 3 (by decide), pathBlocks_clique 3 3 (by decide)⟩,
    pathBlocks_not_surjective⟩

/-! ### The edgeless graph: singleton blocks -/

/-- On three vertices with no edges, the three singleton blocks are cliques. -/
private theorem edgeless_feasible :
    PartitionIntoCliquesFeasible ((3, [], 3) : PartitionIntoCliquesInstance) :=
  ⟨3, le_rfl, id, fun _ _ hu _ hv huv => absurd (hu.trans hv.symm) huv⟩

/-- Two blocks are too few: two of the three vertices share one, and they are not adjacent. -/
private theorem edgeless_two_infeasible :
    ¬ PartitionIntoCliquesFeasible ((3, [], 2) : PartitionIntoCliquesInstance) := by
  rintro ⟨k, hk, c, hc⟩
  have hadj : ∀ u v : Fin 3, ¬ (Graph ((3, [], 2) : PartitionIntoCliquesInstance)).Adj u v :=
    fun u v h => by simp [graph_adj] at h
  have key : ∀ u v : Fin 3, u ≠ v → c u ≠ c v := fun u v huv h =>
    hadj u v (hc (c v) h rfl huv)
  change k ≤ 2 at hk
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact (c 0).elim0
  · exact key 0 1 (by decide) (Subsingleton.elim _ _)
  · have : ∀ a b d : Fin 2, a = b ∨ a = d ∨ b = d := by decide
    rcases this (c 0) (c 1) (c 2) with h | h | h
    · exact key 0 1 (by decide) h
    · exact key 0 2 (by decide) h
    · exact key 1 2 (by decide) h

example : WellFormed ((3, [], 3) : PartitionIntoCliquesInstance) ∧
    WellFormed ((3, [], 2) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; constructor <;> decide

/-- The decision problem accepts the edgeless graph with three blocks and rejects it with two. -/
example :
    partitionIntoCliquesDec (bitEncode ((3, [], 3) : PartitionIntoCliquesInstance)) = true ∧
      partitionIntoCliquesDec (bitEncode ((3, [], 2) : PartitionIntoCliquesInstance)) =
        false := by
  have h3 : WellFormed ((3, [], 3) : PartitionIntoCliquesInstance) := by unfold WellFormed; decide
  simp [partitionIntoCliquesDec, h3, edgeless_feasible, edgeless_two_infeasible]

/-- A graph with a vertex has no partition into `Fin 0`, so the bound `0` is infeasible. -/
example : ¬ PartitionIntoCliquesFeasible ((1, [], 0) : PartitionIntoCliquesInstance) := by
  rintro ⟨k, hk, c, -⟩
  change k ≤ 0 at hk
  obtain rfl : k = 0 := by omega
  exact (c 0).elim0

/-! ### The bound: `0 < K` and `K ≤ n` -/

/-- The empty graph with the bound `0` is feasible, with no blocks at all. -/
private theorem empty_feasible :
    PartitionIntoCliquesFeasible ((0, [], 0) : PartitionIntoCliquesInstance) :=
  ⟨0, le_rfl, Fin.elim0, fun j => j.elim0⟩

/-- It is malformed only because the bound is not positive: its edge list is simple and
`0 ≤ 0`. -/
private theorem empty_malformed : ¬ WellFormed ((0, [], 0) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; decide

example : let i : PartitionIntoCliquesInstance := (0, [], 0)
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
      ¬ 0 < i.2.2 ∧ i.2.2 ≤ i.1 := by
  decide

/-- One edge with the bound `3` is feasible, as one clique. -/
private theorem edge_three_feasible :
    PartitionIntoCliquesFeasible ((2, [(0, 1)], 3) : PartitionIntoCliquesInstance) := by
  refine ⟨1, by decide, fun _ => 0, fun _ u _ v _ huv => (graph_adj _ u v).2 ⟨huv, ?_⟩⟩
  fin_cases u <;> fin_cases v <;> simp_all

/-- It is malformed only because the bound exceeds the two vertices. -/
private theorem edge_three_malformed :
    ¬ WellFormed ((2, [(0, 1)], 3) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; decide

example : WellFormed ((2, [(0, 1)], 2) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; decide

/-- The decision problem rejects the encodings of both feasible instances. -/
example :
    partitionIntoCliquesDec (bitEncode ((0, [], 0) : PartitionIntoCliquesInstance)) = false ∧
      partitionIntoCliquesDec (bitEncode ((2, [(0, 1)], 3) : PartitionIntoCliquesInstance)) =
        false := by
  simp [partitionIntoCliquesDec, empty_malformed, edge_three_malformed]

/-! ### Malformed edge lists -/

/-- On two vertices, one block holding both vertices is a clique whenever the edge list holds
`(0, 1)`. -/
private theorem two_one_block (es : List (ℕ × ℕ)) (h : (0, 1) ∈ es) :
    PartitionIntoCliquesFeasible ((2, es, 1) : PartitionIntoCliquesInstance) := by
  refine ⟨1, le_rfl, fun _ => 0, fun _ u _ v _ huv => (graph_adj _ u v).2 ⟨huv, ?_⟩⟩
  fin_cases u <;> fin_cases v <;> simp_all

/-- A repeated edge, an edge in both directions, and a first or a second endpoint outside the
vertices, each beside the edge `(0, 1)`, and a loop on one vertex: each instance is feasible
with one block. -/
private theorem malformed_feasible :
    PartitionIntoCliquesFeasible ((2, [(0, 1), (0, 1)], 1) : PartitionIntoCliquesInstance) ∧
      PartitionIntoCliquesFeasible ((2, [(0, 1), (1, 0)], 1) : PartitionIntoCliquesInstance) ∧
      PartitionIntoCliquesFeasible ((2, [(0, 1), (5, 0)], 1) : PartitionIntoCliquesInstance) ∧
      PartitionIntoCliquesFeasible ((2, [(0, 1), (0, 5)], 1) : PartitionIntoCliquesInstance) ∧
      PartitionIntoCliquesFeasible ((1, [(0, 0)], 1) : PartitionIntoCliquesInstance) :=
  ⟨two_one_block _ (by simp), two_one_block _ (by simp), two_one_block _ (by simp),
    two_one_block _ (by simp),
    ⟨1, le_rfl, fun _ => 0, fun _ u _ v _ huv => absurd (Subsingleton.elim u v) huv⟩⟩

/-- Each of those instances is malformed. A loop `(u, u)` is its own reversal, so the clause
excluding reversed duplicates already excludes it as well as `u ≠ v` does. -/
private theorem malformed :
    ¬ WellFormed ((2, [(0, 1), (0, 1)], 1) : PartitionIntoCliquesInstance) ∧
      ¬ WellFormed ((2, [(0, 1), (1, 0)], 1) : PartitionIntoCliquesInstance) ∧
      ¬ WellFormed ((2, [(0, 1), (5, 0)], 1) : PartitionIntoCliquesInstance) ∧
      ¬ WellFormed ((2, [(0, 1), (0, 5)], 1) : PartitionIntoCliquesInstance) ∧
      ¬ WellFormed ((1, [(0, 0)], 1) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Their bounds are positive and at most the vertices, and without the offending entry each
is well formed: the edge list alone makes them malformed. -/
example : WellFormed ((2, [(0, 1)], 1) : PartitionIntoCliquesInstance) ∧
    WellFormed ((1, [], 1) : PartitionIntoCliquesInstance) := by
  unfold WellFormed; constructor <;> decide

/-- The decision problem rejects the encodings of those feasible but malformed instances, so
`WellFormed` alone rejects them. -/
example :
    partitionIntoCliquesDec
          (bitEncode ((2, [(0, 1), (0, 1)], 1) : PartitionIntoCliquesInstance)) = false ∧
      partitionIntoCliquesDec
          (bitEncode ((2, [(0, 1), (1, 0)], 1) : PartitionIntoCliquesInstance)) = false ∧
      partitionIntoCliquesDec
          (bitEncode ((2, [(0, 1), (5, 0)], 1) : PartitionIntoCliquesInstance)) = false ∧
      partitionIntoCliquesDec
          (bitEncode ((2, [(0, 1), (0, 5)], 1) : PartitionIntoCliquesInstance)) = false ∧
      partitionIntoCliquesDec (bitEncode ((1, [(0, 0)], 1) : PartitionIntoCliquesInstance)) =
        false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := malformed
  simp [partitionIntoCliquesDec, h1, h2, h3, h4, h5]

/-! ### Decoding -/

/-- Encoding then decoding an instance gives it back. -/
example : bitDecode (bitEncode (path 2)) = some (path 2) := bitDecode_bitEncode _

/-- The empty bitstring decodes to no instance, and the decision problem rejects it. -/
example : partitionIntoCliquesDec [] = false := by
  have h : bitDecode (α := PartitionIntoCliquesInstance) [] = none := rfl
  simp [partitionIntoCliquesDec, h]

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
