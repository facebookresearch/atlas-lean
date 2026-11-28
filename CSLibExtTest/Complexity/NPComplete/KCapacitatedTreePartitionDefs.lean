/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KCapacitatedTreePartitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints)

private theorem dec_bitEncode (i : BoundedDiameterSpanningTreeInstance) :
    kCapacitatedTreePartitionDec (bitEncode i) = true ↔
      WellFormed i ∧ KCapacitatedTreePartitionFeasible i := by
  simp [kCapacitatedTreePartitionDec, bitDecode_bitEncode]

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

/-- One edge `{0, 1}` of weight `5`, `k = 2`, `K = 5`: the edge itself is a spanning tree with
both vertices in its one component. -/
example :
    kCapacitatedTreePartitionDec
      (bitEncode ((2, [(0, 1, 5)], 2, 5) : BoundedDiameterSpanningTreeInstance)) = true := by
  rw [dec_bitEncode]
  have hadj : (forest ((2, [(0, 1, 5)], 2, 5) : BoundedDiameterSpanningTreeInstance)
      [(0, 1, 5)]).Adj 0 1 := by
    unfold forest Cslib.Complexity.Karp.edgeGraph
    rw [SimpleGraph.fromRel_adj]
    decide
  have htree := isTree_of_two _ 0 1 hadj fin_two
  refine ⟨by unfold WellFormed endpoints; decide, [(0, 1, 5)], List.Sublist.refl _,
    htree.isAcyclic, fun v => ?_, by decide⟩
  have huniv : ((forest ((2, [(0, 1, 5)], 2, 5) : BoundedDiameterSpanningTreeInstance)
      [(0, 1, 5)]).connectedComponentMk v).supp = Set.univ := by
    ext w
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
    exact SimpleGraph.ConnectedComponent.eq.2 (htree.1.preconnected w v)
  rw [huniv, Nat.card_univ]
  simp

/-- The same graph with `K = 4`: keeping the edge costs `5 > 4`, and dropping it leaves
components of one vertex, fewer than `k = 2`. -/
example :
    kCapacitatedTreePartitionDec
      (bitEncode ((2, [(0, 1, 5)], 2, 4) : BoundedDiameterSpanningTreeInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, F, hsub, -, hcard, hweight⟩
  rcases List.sublist_singleton.1 hsub with rfl | rfl
  · have hsupp : ((forest ((2, [(0, 1, 5)], 2, 4) : BoundedDiameterSpanningTreeInstance)
        []).connectedComponentMk 0).supp = {0} := by
      ext w
      simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff,
        SimpleGraph.ConnectedComponent.eq]
      constructor
      · rintro ⟨p⟩
        cases p with
        | nil => rfl
        | cons h _ =>
          unfold forest Cslib.Complexity.Karp.edgeGraph at h
          rw [SimpleGraph.fromRel_adj] at h
          simp at h
      · rintro rfl
        exact SimpleGraph.Reachable.refl _
    have := hcard 0
    rw [hsupp] at this
    simp at this
  · simp at hweight

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := BoundedDiameterSpanningTreeInstance) bits = none) :
    kCapacitatedTreePartitionDec bits = false := by
  simp [kCapacitatedTreePartitionDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kCapacitatedTreePartitionDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition
