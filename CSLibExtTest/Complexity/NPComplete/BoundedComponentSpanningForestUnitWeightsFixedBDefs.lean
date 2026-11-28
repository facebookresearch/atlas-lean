/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedBDefs

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BoundedComponentSpanningForest (BoundedComponentSpanningForestFeasible Graph)

/-- On an encoded instance the language for the bound `B` is well-formedness and feasibility. -/
private theorem dec_bitEncode (B : ℕ) (i : FixedBoundInstance) :
    boundedComponentSpanningForestUnitWeightsDec B (bitEncode i) = true ↔
      WellFormed B i ∧ BoundedComponentSpanningForestFeasible (withBound i B) := by
  simp [boundedComponentSpanningForestUnitWeightsDec, bitDecode_bitEncode]

/-- The path `0 - 1 - 2` with unit weights and at most `K` parts. -/
private abbrev path3 (K : ℕ) : FixedBoundInstance := (3, [(0, 1), (1, 2)], [1, 1, 1], K)

private theorem path3_two_wellFormed : WellFormed 2 (path3 2) := by
  unfold WellFormed BoundedComponentSpanningForest.WellFormed; decide

private theorem path3_one_wellFormed : WellFormed 3 (path3 1) := by
  unfold WellFormed BoundedComponentSpanningForest.WellFormed; decide

example : WellFormed 2 (path3 1) := by
  unfold WellFormed BoundedComponentSpanningForest.WellFormed; decide

/-- The parts `{0, 1}` and `{2}`. -/
private def split : Fin 3 → Fin 2 := fun v => if (v : ℕ) = 2 then 1 else 0

/-- Both parts of `split` induce connected subgraphs of the path. -/
private theorem split_connected (K B : ℕ) (j : Fin 2) :
    ((Graph (withBound (path3 K) B)).induce {v | split v = j}).Connected := by
  fin_cases j
  · rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨⟨0, by decide⟩⟩⟩
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [Set.mem_ofPred_eq] at hu hv
    revert hu hv
    fin_cases u <;> fin_cases v <;> intro hu hv <;> try exact absurd hu (by decide)
    all_goals first
      | exact absurd hv (by decide)
      | rfl
      | exact SimpleGraph.Adj.reachable
          (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
  · rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨⟨2, by decide⟩⟩⟩
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [Set.mem_ofPred_eq] at hu hv
    revert hu hv
    fin_cases u <;> fin_cases v <;> intro hu hv <;> try exact absurd hu (by decide)
    all_goals first
      | exact absurd hv (by decide)
      | rfl

/-- The whole path, as the single part of a constant assignment, is connected. -/
private theorem whole_connected (K B : ℕ) (c : Fin 3 → Fin 1) :
    ((Graph (withBound (path3 K) B)).induce {v | c v = 0}).Connected := by
  have hc : ∀ v, c v = 0 := fun v => Fin.ext (Nat.lt_one_iff.1 (c v).isLt)
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨1, hc 1⟩⟩⟩
  have hr : ∀ v : {v | c v = 0}, ((Graph (withBound (path3 K) B)).induce {v | c v = 0}).Reachable
      ⟨1, hc 1⟩ v := by
    rintro ⟨v, hv⟩
    fin_cases v
    · exact SimpleGraph.Adj.reachable (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
    · rfl
    · exact SimpleGraph.Adj.reachable (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
  exact fun u v => (hr u).symm.trans (hr v)

/-- Yes-instance at `B = 2`: the parts `{0, 1}` and `{2}` are connected and have weights at
most `2`. -/
example : boundedComponentSpanningForestUnitWeightsDec 2 (bitEncode (path3 2)) = true := by
  refine (dec_bitEncode 2 _).2 ⟨path3_two_wellFormed, 2, le_rfl, split, ?_,
    fun j => ⟨split_connected 2 2 j, ?_⟩⟩
  · intro j
    fin_cases j
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩
  · fin_cases j <;> decide

/-- Yes-instance at `B = 3`: the whole path is one part of weight `3`. -/
example : boundedComponentSpanningForestUnitWeightsDec 3 (bitEncode (path3 1)) = true := by
  refine (dec_bitEncode 3 _).2 ⟨path3_one_wellFormed, 1, le_rfl, fun _ => 0,
    fun j => ⟨0, Fin.ext (Nat.lt_one_iff.1 j.isLt).symm⟩, fun j => ?_⟩
  obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.1 j.isLt)
  exact ⟨whole_connected 1 3 _, by decide⟩

/-- At `B = 2` one part cannot hold the three unit vertices. -/
private theorem path3_one_not_feasible :
    ¬ BoundedComponentSpanningForestFeasible (withBound (path3 1) 2) := by
  rintro ⟨k, hk, c, -, h⟩
  obtain _ | _ | k := k
  · exact (c 0).elim0
  · have hc : ∀ v, c v = 0 := fun v => Fin.ext (Nat.lt_one_iff.1 (c v).isLt)
    have := (h 0).2
    simp only [hc] at this
    revert this
    decide
  · have : k + 1 + 1 ≤ 1 := hk
    omega

/-- No-instance at `B = 2`: well formed, but the single allowed part would weigh `3`. -/
example : boundedComponentSpanningForestUnitWeightsDec 2 (bitEncode (path3 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode 2 _).1 h).2

/-- Malformed: a vertex weight `2` is rejected even at a bound `B = 4` that it would meet. -/
example : boundedComponentSpanningForestUnitWeightsDec 4
    (bitEncode ((3, [(0, 1), (1, 2)], [1, 2, 1], 1) : FixedBoundInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode 4 _).1 h).1
  revert this
  unfold WellFormed BoundedComponentSpanningForest.WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := FixedBoundInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`, at every bound. -/
example (B : ℕ) : boundedComponentSpanningForestUnitWeightsDec B [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB
