/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BoundedComponentSpanningForestDefs

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BoundedComponentSpanningForestInstance) :
    boundedComponentSpanningForestDec (bitEncode i) = true ↔
      WellFormed i ∧ BoundedComponentSpanningForestFeasible i := by
  simp [boundedComponentSpanningForestDec, bitDecode_bitEncode]

/-- The path `0 - 1 - 2` with unit weights, at most `K` parts of weight at most `B`. -/
private abbrev path3 (K B : ℕ) : BoundedComponentSpanningForestInstance :=
  (3, [(0, 1), (1, 2)], [1, 1, 1], K, B)

example : WellFormed (path3 2 2) := by unfold WellFormed; decide

example : WellFormed (path3 1 2) := by unfold WellFormed; decide

/-- The parts `{0, 1}` and `{2}`. -/
private def split : Fin 3 → Fin 2 := fun v => if (v : ℕ) = 2 then 1 else 0

/-- Both parts of `split` induce connected subgraphs of the path. -/
private theorem split_connected (K B : ℕ) (j : Fin 2) :
    ((Graph (path3 K B)).induce {v | split v = j}).Connected := by
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
      | exact SimpleGraph.Adj.reachable (by simp [Graph, Cslib.Complexity.Karp.edgeGraph])
  · rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨⟨2, by decide⟩⟩⟩
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [Set.mem_ofPred_eq] at hu hv
    revert hu hv
    fin_cases u <;> fin_cases v <;> intro hu hv <;> try exact absurd hu (by decide)
    all_goals first
      | exact absurd hv (by decide)
      | rfl

/-- Yes-instance: the parts `{0, 1}` and `{2}` are connected and have weights `2` and `1`. -/
example : boundedComponentSpanningForestDec (bitEncode (path3 2 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, 2, le_rfl, split, ?_, fun j =>
    ⟨split_connected 2 2 j, ?_⟩⟩
  · intro j
    fin_cases j
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩
  · fin_cases j <;> decide

/-- With one part, the part is the whole path, of weight `3`. -/
private theorem path3_one_not_feasible : ¬ BoundedComponentSpanningForestFeasible (path3 1 2) := by
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

/-- No-instance: well formed, but one part of weight at most `2` cannot hold three unit
vertices. -/
example : boundedComponentSpanningForestDec (bitEncode (path3 1 2)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: the part bound `K = 4` exceeds the three vertices. -/
example : boundedComponentSpanningForestDec (bitEncode (path3 4 2)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BoundedComponentSpanningForestInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : boundedComponentSpanningForestDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest
