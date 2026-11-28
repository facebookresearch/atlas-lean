/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricConnectedDominatingSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)

private theorem dec_bitEncode (i : GeometricConnectedDominatingSetInstance) :
    geometricConnectedDominatingSetDec (bitEncode i) = true ↔
      WellFormed i ∧ GeometricConnectedDominatingSetFeasible i := by
  simp [geometricConnectedDominatingSetDec, bitDecode_bitEncode]

/-- A vertex adjacent to every other vertex gives a one-point connected dominating set. -/
private theorem singleton_cds {V : Type*} [DecidableEq V] (G : SimpleGraph V) (x : V)
    (hx : ∀ v, v = x ∨ G.Adj x v) :
    ({x} : Finset V).card ≤ 1 ∧ G.IsDominating ↑({x} : Finset V) ∧
      (G.induce (↑({x} : Finset V) : Set V)).Connected := by
  refine ⟨by simp, fun v => ?_, (SimpleGraph.connected_iff _).2 ⟨?_, ⟨⟨x, by simp⟩⟩⟩⟩
  · rcases hx v with rfl | h
    · exact Or.inl (by simp)
    · exact Or.inr ⟨x, by simp, h⟩
  · rintro ⟨u, hu⟩ ⟨w, hw⟩
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
    subst hu hw
    exact SimpleGraph.Reachable.refl _

/-- When no vertex is adjacent to all others, no set of at most one vertex dominates. -/
private theorem not_dominating_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (v₀ : Fin n)
    (P' : Finset (Fin n)) (hc : P'.card ≤ 1) (hd : G.IsDominating ↑P')
    (hkey : ∀ x, ∃ v, v ≠ x ∧ ¬ G.Adj x v) : False := by
  rcases P'.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rcases hd v₀ with h | ⟨u, hu, -⟩ <;> simp at *
  · obtain ⟨v, hvx, hadj⟩ := hkey x
    have hall := Finset.card_le_one.1 hc
    rcases hd v with h | ⟨u, hu, h⟩
    · exact hvx (hall v h x hx)
    · exact hadj (hall u hu x hx ▸ h)

/-- Points `(0, 0)`, `(1, 0)`, `(2, 0)` with `B = 1`, `K = 1`: the middle point alone is a
connected dominating set of the distance-`1` path. -/
example :
    geometricConnectedDominatingSetDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0))], 1, 1) :
        GeometricConnectedDominatingSetInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, {1}, singleton_cds _ 1 fun v => ?_⟩
  unfold Graph
  rw [SimpleGraph.fromRel_adj]
  revert v
  unfold sqDist point toInt
  decide

/-- Points `(0, 0)`, `(1, 0)`, `(2, 0)`, `(3, 0)` with `B = 1`, `K = 1`: no point is within
distance `1` of all the others, so no single point dominates the path. -/
example :
    geometricConnectedDominatingSetDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0)), ((3, 0), (0, 0))],
        1, 1) : GeometricConnectedDominatingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, P', hc, hd, -⟩
  refine not_dominating_le_one _ 0 P' hc hd fun x => ?_
  unfold Graph
  simp only [SimpleGraph.fromRel_adj]
  revert x
  unfold sqDist point toInt
  decide

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricConnectedDominatingSetInstance) bits = none) :
    geometricConnectedDominatingSetDec bits = false := by
  simp [geometricConnectedDominatingSetDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : geometricConnectedDominatingSetDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet
