/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BoundedDiameterAugmentationDefs

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)
open SimpleGraph

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BoundedDiameterAugmentationInstance) :
    boundedDiameterAugmentationDec (bitEncode i) = true ↔
      WellFormed i ∧ BoundedDiameterAugmentationFeasible i := by
  simp [boundedDiameterAugmentationDec, bitDecode_bitEncode]

/-- The path `0 - 1 - 2` (vertex count written as the list `u`), diameter bound `1`, one added
edge. -/
private abbrev path3 (u : List Bool) : BoundedDiameterAugmentationInstance :=
  (u, [(0, 1), (1, 2)], 1, 1)

/-- Three isolated vertices, diameter bound `1`, two added edges. -/
private abbrev empty3 : BoundedDiameterAugmentationInstance := ([true, true, true], [], 1, 2)

example : WellFormed (path3 [true, true, true]) := by unfold WellFormed; decide

example : WellFormed empty3 := by unfold WellFormed; decide

/-- Adding the edge `{0, 2}` to the path gives a graph of diameter `1`, whatever bits write the
vertex count `3`. -/
private theorem path3_feasible (u : List Bool) (hu : u.length = 3) :
    BoundedDiameterAugmentationFeasible (path3 u) := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hu
  refine ⟨fromEdgeSet {s(0, 2)}, ?_, ?_⟩
  · rw [edgeSet_fromEdgeSet]
    exact (Set.ncard_le_ncard Set.sdiff_subset (Set.finite_singleton _)).trans
      (Set.ncard_singleton _).le
  · refine ediam_le_iff.2 fun x y => edist_le_one_iff_adj_or_eq.2 ?_
    fin_cases x <;> fin_cases y <;> simp [Graph, edgeGraph, fromEdgeSet_adj]

/-- Yes-instance: one added edge closes the path into a triangle of diameter `1`. -/
example : boundedDiameterAugmentationDec (bitEncode (path3 [true, true, true])) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, path3_feasible _ rfl⟩

/-- Three isolated vertices need all three pairs added to reach diameter `1`. -/
private theorem empty3_not_feasible : ¬ BoundedDiameterAugmentationFeasible empty3 := by
  rintro ⟨H, hcard, hdiam⟩
  have hadj : ∀ x y : Fin 3, x ≠ y → H.Adj x y := by
    intro x y hxy
    have h := edist_le_one_iff_adj_or_eq.1 ((ediam_le_iff.1 hdiam) x y)
    simpa [Graph, edgeGraph, hxy] using h
  have hsub : ((({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))) ⊆
      H.edgeSet := by
    intro e he
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl <;> exact hadj _ _ (by decide)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h3
  have : ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))).card = 3 := by decide
  have h2 : H.edgeSet.ncard ≤ 2 := hcard
  omega

/-- No-instance: well formed, but two added edges cannot make three isolated vertices
pairwise adjacent. -/
example : boundedDiameterAugmentationDec (bitEncode empty3) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => empty3_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: the vertex count must be written with `true` bits only, so this instance is
rejected although its graph is the feasible path on three vertices. -/
example : boundedDiameterAugmentationDec (bitEncode (path3 [true, false, true])) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

example : BoundedDiameterAugmentationFeasible (path3 [true, false, true]) := path3_feasible _ rfl

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BoundedDiameterAugmentationInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : boundedDiameterAugmentationDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation
