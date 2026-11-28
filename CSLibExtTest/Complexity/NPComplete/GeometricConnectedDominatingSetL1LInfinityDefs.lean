/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinityDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)
open GeometricConnectedDominatingSet (GeometricConnectedDominatingSetInstance WellFormed)
open GeometricTravelingSalesmanLInfinity (chebyshevDist)
open RectilinearTravelingSalesman (rectilinearDist)

private theorem l1Dec_bitEncode (i : GeometricConnectedDominatingSetInstance) :
    l1Dec (bitEncode i) = true ↔ WellFormed i ∧ L1Feasible i := by
  simp [l1Dec, bitDecode_bitEncode]

private theorem lInfinityDec_bitEncode (i : GeometricConnectedDominatingSetInstance) :
    lInfinityDec (bitEncode i) = true ↔ WellFormed i ∧ LInfinityFeasible i := by
  simp [lInfinityDec, bitDecode_bitEncode]

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

/-- `L₁`: points `(0, 0)`, `(1, 0)`, `(2, 0)` with `B = 1`, `K = 1`; the middle point alone
dominates. -/
example :
    l1Dec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0))], 1, 1) :
        GeometricConnectedDominatingSetInstance)) = true := by
  rw [l1Dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, {1}, singleton_cds _ 1 fun v => ?_⟩
  unfold l1Graph
  rw [SimpleGraph.fromRel_adj]
  revert v
  unfold rectilinearDist point toInt
  decide

/-- `L₁`: the diagonal points `(0, 0)`, `(1, 1)`, `(2, 2)` with `B = 1`, `K = 1` are pairwise
at `L₁` distance at least `2`, so no single point dominates. -/
example :
    l1Dec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0)), ((2, 0), (2, 0))], 1, 1) :
        GeometricConnectedDominatingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, l1Dec_bitEncode]
  rintro ⟨-, P', hc, hd, -⟩
  refine not_dominating_le_one _ 0 P' hc hd fun x => ?_
  unfold l1Graph
  simp only [SimpleGraph.fromRel_adj]
  revert x
  unfold rectilinearDist point toInt
  decide

/-- `L∞`: the same diagonal points `(0, 0)`, `(1, 1)`, `(2, 2)` are at `L∞` distance `1` from
the middle one, which alone dominates; the metric decides between acceptance and rejection. -/
example :
    lInfinityDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0)), ((2, 0), (2, 0))], 1, 1) :
        GeometricConnectedDominatingSetInstance)) = true := by
  rw [lInfinityDec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, {1}, singleton_cds _ 1 fun v => ?_⟩
  unfold lInfinityGraph
  rw [SimpleGraph.fromRel_adj]
  revert v
  unfold chebyshevDist point toInt
  decide

/-- `L∞`: points `(0, 0)`, `(1, 0)`, `(2, 0)`, `(3, 0)` with `B = 1`, `K = 1`; no single point
dominates the path. -/
example :
    lInfinityDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0)), ((3, 0), (0, 0))],
        1, 1) : GeometricConnectedDominatingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, lInfinityDec_bitEncode]
  rintro ⟨-, P', hc, hd, -⟩
  refine not_dominating_le_one _ 0 P' hc hd fun x => ?_
  unfold lInfinityGraph
  simp only [SimpleGraph.fromRel_adj]
  revert x
  unfold chebyshevDist point toInt
  decide

private theorem l1_rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricConnectedDominatingSetInstance) bits = none) :
    l1Dec bits = false := by
  simp [l1Dec, h]

private theorem lInfinity_rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricConnectedDominatingSetInstance) bits = none) :
    lInfinityDec bits = false := by
  simp [lInfinityDec, h]

/-- A lone continuation bit is a truncated instance encoding (`L₁`). -/
example : l1Dec [true] = false :=
  l1_rejects_undecodable [true] rfl

/-- A lone continuation bit is a truncated instance encoding (`L∞`). -/
example : lInfinityDec [true] = false :=
  lInfinity_rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSetL1LInfinity
