/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeDefs
import Mathlib.Algebra.BigOperators.Fin

namespace MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem dec_bitEncode (i : GeometricCapacitatedSpanningTreeInstance) :
    geometricCapacitatedSpanningTreeDec (bitEncode i) = true ↔
      WellFormed i ∧ GeometricCapacitatedSpanningTreeFeasible i := by
  simp [geometricCapacitatedSpanningTreeDec, bitDecode_bitEncode]

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

/-- `⌈√25⌉ = 5`: the discretized length of the segment from `(0, 0)` to `(3, 4)`. -/
private theorem pointDist_three_four (r : List ℕ) (c B : ℕ) :
    pointDist (([((0, 0), (0, 0)), ((3, 0), (4, 0))], 0, r, c, B) :
      GeometricCapacitatedSpanningTreeInstance) 0 1 = 5 := by
  have h : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [pointDist, points, GeometricTravelingSalesman.discreteDist,
    GeometricTravelingSalesman.point, GeometricTravelingSalesman.toInt]
  norm_num [h]

/-- A spanning tree of two vertices contains the edge between them. -/
private theorem adj_of_isTree_two (T : SimpleGraph (Fin 2)) (hT : T.IsTree) : T.Adj 0 1 := by
  obtain ⟨p⟩ := hT.1.preconnected 0 1
  have hsnd := SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne (p := p) (by decide))
  rcases fin_two p.snd with h | h
  · exact absurd h.symm hsnd.ne
  · rwa [h] at hsnd

open Classical in
/-- The complete graph on the two points `p₀ = (0, 0)` and `(3, 4)` is a spanning tree of length
`5 ≤ B = 5`; its edge carries the requirement `2 ≤ c = 2` of `(3, 4)`. -/
private theorem feasible_two :
    GeometricCapacitatedSpanningTreeFeasible
      (([((0, 0), (0, 0)), ((3, 0), (4, 0))], 0, [0, 2], 2, 5) :
        GeometricCapacitatedSpanningTreeInstance) := by
  refine ⟨by decide, ⊤, isTree_of_two _ 0 1 (by simp) fin_two, ?_, fun e _ => ?_⟩
  · simp [pointDist_three_four]
  · refine (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ?_
    simp [Fin.sum_univ_two]

open Classical in
/-- With requirement `3` at `(3, 4)` and capacity `c = 2`, the edge of every spanning tree lies
on the path from `(3, 4)` to `p₀` and carries `3 > 2`. -/
private theorem not_feasible_capacity :
    ¬ GeometricCapacitatedSpanningTreeFeasible
      (([((0, 0), (0, 0)), ((3, 0), (4, 0))], 0, [0, 3], 2, 9) :
        GeometricCapacitatedSpanningTreeInstance) := by
  rintro ⟨hp, T, hT, -, hcap⟩
  have h01 := adj_of_isTree_two T hT
  have hmem : (1 : Fin 2) ∈ Finset.univ.filter (fun u => ∃ p : T.Walk u ⟨0, hp⟩,
      p.IsPath ∧ s(0, 1) ∈ p.edges) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
      SimpleGraph.Walk.cons h01.symm SimpleGraph.Walk.nil, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simp⟩
    · simp [Sym2.eq_swap]
  have := (Finset.single_le_sum (f := fun u : Fin 2 =>
    ([0, 3] : List ℕ).getD (u : ℕ) 0) (fun _ _ => Nat.zero_le _) hmem).trans
    (hcap s(0, 1) h01)
  simp at this

/-- Points `p₀ = (0, 0)` and `(3, 4)` with requirements `0, 2`, capacity `c = 2`, bound `B = 5`:
the one-edge tree is accepted. -/
example :
    geometricCapacitatedSpanningTreeDec
      (bitEncode (([((0, 0), (0, 0)), ((3, 0), (4, 0))], 0, [0, 2], 2, 5) :
        GeometricCapacitatedSpanningTreeInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨?_, feasible_two⟩
  unfold WellFormed points GeometricTravelingSalesman.point GeometricTravelingSalesman.toInt
  decide

/-- The same points with requirement `3` at `(3, 4)`, capacity `c = 2` and a generous bound
`B = 9`: the capacity condition rejects the instance. -/
example :
    geometricCapacitatedSpanningTreeDec
      (bitEncode (([((0, 0), (0, 0)), ((3, 0), (4, 0))], 0, [0, 3], 2, 9) :
        GeometricCapacitatedSpanningTreeInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  exact fun h => not_feasible_capacity h.2

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricCapacitatedSpanningTreeInstance) bits = none) :
    geometricCapacitatedSpanningTreeDec bits = false := by
  simp [geometricCapacitatedSpanningTreeDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : geometricCapacitatedSpanningTreeDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree
