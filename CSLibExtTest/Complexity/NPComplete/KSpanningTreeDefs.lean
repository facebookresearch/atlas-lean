/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KSpanningTreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.KSpanningTree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints Graph weight)

private theorem dec_bitEncode (i : BoundedDiameterSpanningTreeInstance) :
    kSpanningTreeDec (bitEncode i) = true ↔ WellFormed i ∧ KSpanningTreeFeasible i := by
  simp [kSpanningTreeDec, bitDecode_bitEncode]

/-- A graph whose vertices are all among `x` and `y` has no cycle: a cycle needs three distinct
vertices. -/
private theorem isAcyclic_of_two {V : Type*} (G : SimpleGraph V) (x y : V)
    (hall : ∀ v, v = x ∨ v = y) : G.IsAcyclic := by
  intro v c hc
  have h3 := hc.isCircuit.three_le_length
  have hsub : c.support.tail ⊆ [x, y] := fun w _ => by rcases hall w with rfl | rfl <;> simp
  have hl := (List.subperm_of_subset hc.support_nodup hsub).length_le
  simp only [List.length_tail, SimpleGraph.Walk.length_support, List.length_cons,
    List.length_nil] at hl
  omega

/-- An edge `x y` on a vertex type with no other vertices is a tree. -/
private theorem isTree_of_two {V : Type*} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (hall : ∀ v, v = x ∨ v = y) : G.IsTree := by
  refine ⟨(SimpleGraph.connected_iff G).2 ⟨fun u v => ?_, ⟨x⟩⟩, isAcyclic_of_two G x y hall⟩
  rcases hall u with rfl | rfl <;> rcases hall v with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hxy.reachable
  · exact hxy.symm.reachable
  · exact SimpleGraph.Reachable.refl _

private theorem fin_two (v : Fin 2) : v = 0 ∨ v = 1 := by
  revert v; decide

/-- The edge `{0, 1}` of the instance graph (its only edge). -/
private theorem adj01 (w : ℕ) :
    (Graph ((2, [(0, 1, w)], 2, w) : BoundedDiameterSpanningTreeInstance)).Adj 0 1 := by
  unfold Graph Cslib.Complexity.Karp.edgeGraph endpoints
  rw [SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl (by simp)⟩

/-- One edge `{0, 1}` of weight `3`, `k = 2`, `K = 3`: the edge is a subtree with two nodes and
weight `3`. -/
example :
    kSpanningTreeDec
      (bitEncode ((2, [(0, 1, 3)], 2, 3) : BoundedDiameterSpanningTreeInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed endpoints; decide, (Graph _).subgraphOfAdj (adj01 3), ?_, ?_, ?_⟩
  · refine isTree_of_two _ ⟨0, by simp⟩ ⟨1, by simp⟩ ?_ ?_
    · rw [SimpleGraph.Subgraph.coe_adj]
      exact SimpleGraph.subgraphOfAdj_adj_self _
    · rintro ⟨v, hv⟩
      rw [SimpleGraph.subgraphOfAdj_verts] at hv
      rcases hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rw [SimpleGraph.subgraphOfAdj_verts, Set.ncard_pair (by decide)]
  · rw [SimpleGraph.edgeSet_subgraphOfAdj, finsum_mem_singleton]
    unfold weight
    decide

/-- A set of vertices of `Fin 2` with at least two elements contains every vertex. -/
private theorem mem_of_two_le_ncard (S : Set (Fin 2)) (h : 2 ≤ S.ncard) (v : Fin 2) : v ∈ S := by
  by_contra hv
  have hsub : S ⊆ {1 - v} := by
    intro w hw
    rcases fin_two v with rfl | rfl <;> rcases fin_two w with rfl | rfl <;> simp_all
  have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at this
  omega

/-- One edge `{0, 1}` of weight `6`, `k = 2`, `K = 5`: a subtree with two nodes must contain the
edge, of weight `6 > 5`. -/
example :
    kSpanningTreeDec
      (bitEncode ((2, [(0, 1, 6)], 2, 5) : BoundedDiameterSpanningTreeInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, T, hT, hcard, hw⟩
  have h0 := mem_of_two_le_ncard _ hcard 0
  have h1 := mem_of_two_le_ncard _ hcard 1
  obtain ⟨p⟩ := hT.1.preconnected ⟨0, h0⟩ ⟨1, h1⟩
  have hsnd := SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne (p := p)
    (by simp [Subtype.ext_iff]))
  rw [SimpleGraph.Subgraph.coe_adj] at hsnd
  have hne := (T.adj_sub hsnd).ne
  have hT01 : T.Adj 0 1 := by
    rcases fin_two p.snd.1 with h | h
    · exact absurd h.symm hne
    · rwa [h] at hsnd
  have hedges : T.edgeSet = {s(0, 1)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_singleton_iff]
      constructor
      · intro hab
        have := (T.adj_sub hab).ne
        rcases fin_two a with rfl | rfl <;> rcases fin_two b with rfl | rfl <;>
          first | exact absurd rfl this | rfl | exact Sym2.eq_swap
      · intro hab
        rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hT01
        · exact hT01.symm
  rw [hedges, finsum_mem_singleton] at hw
  revert hw
  unfold weight
  decide

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := BoundedDiameterSpanningTreeInstance) bits = none) :
    kSpanningTreeDec bits = false := by
  simp [kSpanningTreeDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kSpanningTreeDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.KSpanningTree
