/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CapacitatedSpanningTreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)
open SimpleGraph

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : CapacitatedSpanningTreeInstance) :
    capacitatedSpanningTreeDec (bitEncode i) = true ↔
      WellFormed i ∧ CapacitatedSpanningTreeFeasible i := by
  simp [capacitatedSpanningTreeDec, bitDecode_bitEncode]

/-- The path `0 - 1 - 2` rooted at `v₀ = 0`, with `c({0, 1}) = c`, `c({1, 2}) = 2`, unit
lengths, requirements `0, 1, 1`, and length bound `B`. -/
private abbrev path3 (c B : ℕ) : CapacitatedSpanningTreeInstance :=
  (3, [(0, 1, c, 1), (1, 2, 2, 1)], 0, [0, 1, 1], B)

example : WellFormed (path3 2 2) := by unfold WellFormed endpoints; decide

example : WellFormed (path3 1 2) := by unfold WellFormed endpoints; decide

/-- The path `0 - 1 - 2` as a graph. -/
private abbrev path : SimpleGraph (Fin 3) := edgeGraph 3 [(0, 1), (1, 2)]

private theorem graph_path3 (c B : ℕ) : Graph (path3 c B) = path := rfl

/-- The edges of the path. -/
private theorem path_edgeSet : path.edgeSet = {s(0, 1), s(1, 2)} := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  fin_cases a <;> fin_cases b <;> simp [edgeGraph]

/-- The path is a tree: it is connected and has two edges. -/
private theorem path_isTree : path.IsTree := by
  refine isTree_iff_connected_and_card.2 ⟨?_, ?_⟩
  · have h1 : path.Reachable 1 0 := Adj.reachable (by simp [edgeGraph])
    have h2 : path.Reachable 1 2 := Adj.reachable (by simp [edgeGraph])
    have hr : ∀ v, path.Reachable 1 v := fun v => by
      fin_cases v
      · exact h1
      · rfl
      · exact h2
    exact ⟨fun u v => (hr u).symm.trans (hr v)⟩
  · rw [Nat.card_coe_set_eq, path_edgeSet, Set.ncard_pair (by decide)]
    simp

open Classical in
/-- The path has total length `2`. -/
private theorem path_length (c B : ℕ) :
    ∑ e ∈ path.edgeFinset, edgeLength (path3 c B) e = 2 := by
  have : path.edgeFinset = {s(0, 1), s(1, 2)} :=
    Finset.coe_injective (by simp [path_edgeSet])
  rw [this, Finset.sum_pair (by decide)]
  simp [edgeLength, entry]

open Classical in
/-- Yes-instance: the path itself has length `2`, and each of its edges carries at most the
total requirement `2`, which is its capacity. -/
example : capacitatedSpanningTreeDec (bitEncode (path3 2 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed endpoints; decide, by decide, path,
    (graph_path3 2 2).ge, path_isTree, (path_length 2 2).le, fun e he => ?_⟩
  have htot : ∑ u : Fin 3, (path3 2 2).2.2.2.1.getD u 0 = 2 := by decide
  have hcap : capacity (path3 2 2) e = 2 := by
    rw [path_edgeSet] at he
    rcases he with rfl | rfl <;> decide
  rw [hcap, ← htot]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- If `0` is a leaf of `G` whose neighbour is `1`, then in every connected subgraph `T ≤ G` the
path from any other vertex to `0` ends with the edge `{0, 1}`. -/
private theorem path_through_root_edge {n : ℕ} {G T : SimpleGraph (Fin (n + 2))}
    (hleaf : ∀ x, G.Adj 0 x → x = 1) (hT : T ≤ G) (hc : T.Connected) {u : Fin (n + 2)}
    (hu : u ≠ 0) : ∃ p : T.Walk u 0, p.IsPath ∧ s(0, 1) ∈ p.edges := by
  obtain ⟨p, hp⟩ := (hc.preconnected u 0).exists_isPath
  refine ⟨p, hp, ?_⟩
  have key : ∀ q : T.Walk 0 u, s(0, 1) ∈ q.edges := by
    intro q
    cases q with
    | nil => exact absurd rfl hu
    | cons h q' =>
      obtain rfl := hleaf _ (hT h)
      rw [Walk.edges_cons]
      exact List.mem_cons_self
  have := key p.reverse
  rwa [Walk.edges_reverse, List.mem_reverse] at this

open Classical in
/-- With capacity `1` on `{0, 1}`, every spanning tree must route both other vertices, of total
requirement `2`, through that edge. -/
private theorem path3_one_not_feasible : ¬ CapacitatedSpanningTreeFeasible (path3 1 2) := by
  rintro ⟨hv, T, hT, ht, -, hcap⟩
  have hleaf : ∀ x, (Graph (path3 1 2)).Adj 0 x → x = 1 := by
    intro x hx
    revert hx
    fin_cases x <;> simp [Graph, endpoints, edgeGraph]
  have hthrough : ∀ u : Fin 3, u ≠ 0 → ∃ p : T.Walk u 0, p.IsPath ∧ s(0, 1) ∈ p.edges :=
    fun u hu => path_through_root_edge (n := 1) hleaf hT ht.connected hu
  obtain ⟨p, -, hp⟩ := hthrough 1 (by decide)
  have h : ∑ u ∈ Finset.univ.filter
      (fun u : Fin 3 => ∃ p : T.Walk u 0, p.IsPath ∧ s(0, 1) ∈ p.edges),
      (path3 1 2).2.2.2.1.getD u 0 ≤ capacity (path3 1 2) s(0, 1) :=
    hcap _ (p.edges_subset_edgeSet hp)
  have hsub : Finset.univ.erase (0 : Fin 3) ⊆ Finset.univ.filter
      (fun u : Fin 3 => ∃ p : T.Walk u 0, p.IsPath ∧ s(0, 1) ∈ p.edges) := by
    intro u hu
    simpa using hthrough u (Finset.ne_of_mem_erase hu)
  have hlow := Finset.sum_le_sum_of_subset (f := fun u : Fin 3 => (path3 1 2).2.2.2.1.getD u 0)
    hsub
  have h2 : ∑ u ∈ Finset.univ.erase (0 : Fin 3), (path3 1 2).2.2.2.1.getD u 0 = 2 := by decide
  have h1 : capacity (path3 1 2) s(0, 1) = 1 := by decide
  have := hlow.trans h
  omega

/-- No-instance (capacity): well formed, but the root edge `{0, 1}` of capacity `1` must carry
requirement `2`. -/
example : capacitatedSpanningTreeDec (bitEncode (path3 1 2)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode _).1 h).2

open Classical in
/-- A spanning tree of three vertices has two edges, each an edge of the path, of length `1`.
-/
private theorem tree_length_ge {T : SimpleGraph (Fin 3)} (hT : T ≤ Graph (path3 2 1))
    (ht : T.IsTree) : 2 ≤ ∑ e ∈ T.edgeFinset, edgeLength (path3 2 1) e := by
  have hcard := ht.card_edgeFinset
  simp only [Fintype.card_fin] at hcard
  have hle : ∀ e ∈ T.edgeFinset, 1 ≤ edgeLength (path3 2 1) e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : (Graph (path3 2 1)).Adj a b := hT (by simpa using he)
      revert hab
      fin_cases a <;> fin_cases b <;> simp [Graph, endpoints, edgeGraph, edgeLength, entry]
  have := Finset.card_nsmul_le_sum _ _ _ hle
  simp only [smul_eq_mul, mul_one] at this
  have h2 : T.edgeFinset.card = 2 := by omega
  rw [h2] at this
  exact this

/-- No-instance (length): well formed, but every spanning tree has length at least `2 > 1`. -/
example : capacitatedSpanningTreeDec (bitEncode (path3 2 1)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, -, T, hT, ht, hw, -⟩ := (dec_bitEncode _).1 h
  have h3 : 2 ≤ 1 := (tree_length_ge hT ht).trans (by convert hw)
  omega

/-- Malformed: a requirement list of the wrong length is rejected. -/
example : capacitatedSpanningTreeDec
    (bitEncode ((3, [(0, 1, 2, 1), (1, 2, 2, 1)], 0, [0, 1], 2) :
      CapacitatedSpanningTreeInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed endpoints
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := CapacitatedSpanningTreeInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : capacitatedSpanningTreeDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
