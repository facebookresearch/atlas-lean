/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)
open SimpleGraph

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BoundedDiameterSpanningTreeInstance) :
    boundedDiameterSpanningTreeDec (bitEncode i) = true ↔
      WellFormed i ∧ BoundedDiameterSpanningTreeFeasible i := by
  simp [boundedDiameterSpanningTreeDec, bitDecode_bitEncode]

/-- The triangle with `w({0, 1}) = a`, `w({1, 2}) = 1`, `w({0, 2}) = 2`, bounds `D` and `B`. -/
private abbrev tri (a D B : ℕ) : BoundedDiameterSpanningTreeInstance :=
  (3, [(0, 1, a), (1, 2, 1), (0, 2, 2)], D, B)

example : WellFormed (tri 1 2 2) := by unfold WellFormed endpoints; decide

/-- The path `0 - 1 - 2`. -/
private abbrev path : SimpleGraph (Fin 3) := edgeGraph 3 [(0, 1), (1, 2)]

/-- The edges of the path. -/
private theorem path_edgeSet : path.edgeSet = {s(0, 1), s(1, 2)} := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  fin_cases a <;> fin_cases b <;> simp [edgeGraph]

/-- The path is a spanning tree of the triangle: it is connected and has two edges. -/
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

/-- The path lies in the triangle. -/
private theorem path_le (a D B : ℕ) : path ≤ Graph (tri a D B) := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [Graph, endpoints, edgeGraph]

open Classical in
/-- The path weighs `a + 1`. -/
private theorem path_weight (a D B : ℕ) :
    ∑ e ∈ path.edgeFinset, weight (tri a D B) e = a + 1 := by
  have : path.edgeFinset = {s(0, 1), s(1, 2)} :=
    Finset.coe_injective (by simp [path_edgeSet])
  rw [this, Finset.sum_pair (by decide)]
  simp [weight]

/-- On three vertices every path has at most two edges. -/
private theorem path_length_le {T : SimpleGraph (Fin 3)} {u v : Fin 3} (p : T.Walk u v)
    (hp : p.IsPath) : p.length ≤ 2 := by
  have := hp.length_lt
  simp only [Fintype.card_fin] at this
  omega

/-- Yes-instance: the path `0 - 1 - 2` weighs `2` and has diameter `2`. -/
example : boundedDiameterSpanningTreeDec (bitEncode (tri 1 2 2)) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed endpoints; decide, path, path_le 1 2 2, path_isTree,
    (path_weight 1 2 2).le, fun _ _ p hp => path_length_le p hp⟩

open Classical in
/-- A spanning tree on three vertices has two edges, and every pair of distinct vertices of the
triangle has weight at least `1`. -/
private theorem tree_weight_ge (D B : ℕ) {T : SimpleGraph (Fin 3)} (ht : T.IsTree) :
    2 ≤ ∑ e ∈ T.edgeFinset, weight (tri 1 D B) e := by
  have hcard := ht.card_edgeFinset
  simp only [Fintype.card_fin] at hcard
  have hpos : ∀ a b : Fin 3, a ≠ b → 1 ≤ weight (tri 1 D B) s(a, b) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [weight]
  have hle : ∀ e ∈ T.edgeFinset, 1 ≤ weight (tri 1 D B) e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      exact hpos a b (T.ne_of_adj (by simpa using he))
  have := Finset.card_nsmul_le_sum _ _ _ hle
  simp only [smul_eq_mul, mul_one] at this
  have h2 : T.edgeFinset.card = 2 := by omega
  rw [h2] at this
  exact this

/-- No-instance (weight): well formed, but every spanning tree weighs at least `2 > 1`. -/
example : boundedDiameterSpanningTreeDec (bitEncode (tri 1 2 1)) = false := by
  rw [Bool.eq_false_iff]
  rintro h
  obtain ⟨-, T, -, ht, hw, -⟩ := (dec_bitEncode _).1 h
  have h3 : 2 ≤ 1 := (tree_weight_ge 2 1 ht).trans (by convert hw)
  omega

open Classical in
/-- A spanning tree of three vertices has a path with two edges: otherwise every two vertices
would be adjacent, giving three edges. -/
private theorem tree_not_diam_one {T : SimpleGraph (Fin 3)} (ht : T.IsTree)
    (hd : ∀ (u v : Fin 3) (p : T.Walk u v), p.IsPath → p.length ≤ 1) : False := by
  have hadj : ∀ u v : Fin 3, u ≠ v → T.Adj u v := by
    intro u v huv
    obtain ⟨p, hp⟩ := (ht.connected.preconnected u v).exists_isPath
    have h1 := hd u v p hp
    have h0 : p.length ≠ 0 := fun h => huv (Walk.eq_of_length_eq_zero h)
    exact Walk.adj_of_length_eq_one (p := p) (by omega)
  have hsub : ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) ⊆ T.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> simpa using hadj _ _ (by decide)
  have h3 := Finset.card_le_card hsub
  have hcard := ht.card_edgeFinset
  have : ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 3 := by decide
  simp only [Fintype.card_fin] at hcard
  omega

/-- No-instance (diameter): well formed with a generous budget, but no spanning tree of three
vertices has diameter `1`. -/
example : boundedDiameterSpanningTreeDec (bitEncode (tri 1 1 5)) = false := by
  rw [Bool.eq_false_iff]
  rintro h
  obtain ⟨-, T, -, ht, -, hd⟩ := (dec_bitEncode _).1 h
  exact tree_not_diam_one ht hd

/-- Malformed: the weight `0` is rejected, although the path would then weigh only `1`. -/
example : boundedDiameterSpanningTreeDec (bitEncode (tri 0 2 2)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed endpoints
  decide

example : BoundedDiameterSpanningTreeFeasible (tri 0 2 2) :=
  ⟨path, path_le 0 2 2, path_isTree, by rw [path_weight]; decide,
    fun _ _ p hp => path_length_le p hp⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BoundedDiameterSpanningTreeInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : boundedDiameterSpanningTreeDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree
