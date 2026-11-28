/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DiameterSpanningSubgraphDefs

namespace MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)
open SimpleGraph

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : DiameterSpanningSubgraphInstance) :
    diameterSpanningSubgraphDec (bitEncode i) = true ↔
      WellFormed i ∧ DiameterSpanningSubgraphFeasible i := by
  simp [diameterSpanningSubgraphDec, bitDecode_bitEncode]

/-- The path `0 - 1 - 2` with weights `w({0, 1}) = a`, `w({1, 2}) = 1`, unit lengths, budget
`B` and length bound `K`. -/
private abbrev path3 (a B K : ℕ) : DiameterSpanningSubgraphInstance :=
  (3, [(0, 1, a, 1), (1, 2, 1, 1)], B, K)

example : WellFormed (path3 1 2 2) := by unfold WellFormed endpoints; decide

example : WellFormed (path3 1 1 2) := by unfold WellFormed endpoints; decide

/-- Keeping both edges joins every two vertices by a walk of length at most `2`. -/
private theorem path3_feasible (a B : ℕ) (hB : a + 1 ≤ B) :
    DiameterSpanningSubgraphFeasible (path3 a B 2) := by
  refine ⟨(path3 a B 2).2.1, List.Sublist.refl _, by simpa using hB, fun u v => ?_⟩
  have h01 : (spanning (path3 a B 2) (path3 a B 2).2.1).Adj 0 1 := by
    simp [spanning, endpoints, edgeGraph]
  have h12 : (spanning (path3 a B 2) (path3 a B 2).2.1).Adj 1 2 := by
    simp [spanning, endpoints, edgeGraph]
  fin_cases u <;> fin_cases v
  · exact ⟨.nil, by simp [walkLength]⟩
  · exact ⟨.cons h01 .nil, by simp [walkLength, edgeLength]⟩
  · exact ⟨.cons h01 (.cons h12 .nil), by simp [walkLength, edgeLength]⟩
  · exact ⟨.cons h01.symm .nil, by simp [walkLength, edgeLength]⟩
  · exact ⟨.nil, by simp [walkLength]⟩
  · exact ⟨.cons h12 .nil, by simp [walkLength, edgeLength]⟩
  · exact ⟨.cons h12.symm (.cons h01.symm .nil), by simp [walkLength, edgeLength]⟩
  · exact ⟨.cons h12.symm .nil, by simp [walkLength, edgeLength]⟩
  · exact ⟨.nil, by simp [walkLength]⟩

/-- Yes-instance: both edges (weight `2`) give every pair a walk of length at most `2`. -/
example : diameterSpanningSubgraphDec (bitEncode (path3 1 2 2)) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed endpoints; decide, path3_feasible 1 2 le_rfl⟩

/-- A walk that starts at a vertex without neighbours never leaves it. -/
private theorem walk_from_isolated {V : Type*} {G : SimpleGraph V} {v w : V}
    (hv : ∀ x, ¬ G.Adj v x) (p : G.Walk v w) : w = v := by
  cases p with
  | nil => rfl
  | cons h _ => exact absurd h (hv _)

/-- Within budget `1` at most one of the two edges is kept, so `0` or `2` has no neighbour. -/
private theorem path3_one_not_feasible : ¬ DiameterSpanningSubgraphFeasible (path3 1 1 2) := by
  rintro ⟨E', hsub, hw, hwalk⟩
  have hlen := hsub.length_le
  have hmem : ∀ e ∈ E', e ∈ (path3 1 1 2).2.1 := fun e he => hsub.subset he
  obtain ⟨p⟩ : Nonempty ((spanning (path3 1 1 2) E').Walk 0 2) := ⟨(hwalk 0 2).choose⟩
  match E', hsub, hw, hlen, hmem, p with
  | [], _, _, _, _, p =>
    exact absurd (walk_from_isolated (fun x => by simp [spanning, endpoints, edgeGraph]) p)
      (by decide)
  | [e], _, _, _, hmem, p =>
    have he := hmem e (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have h2 := walk_from_isolated (G := spanning (path3 1 1 2) [(0, 1, 1, 1)]) (v := 2)
        (fun x => by fin_cases x <;> simp [spanning, endpoints, edgeGraph]) p.reverse
      exact absurd h2 (by decide)
    · exact absurd (walk_from_isolated
        (fun x => by fin_cases x <;> simp [spanning, endpoints, edgeGraph]) p) (by decide)
  | [e, f], hsub, hw, _, hmem, _ =>
    have key : ∀ e ∈ (path3 1 1 2).2.1, ∀ f ∈ (path3 1 1 2).2.1,
        [e, f].Sublist (path3 1 1 2).2.1 → ¬ ([e, f].map fun e => e.2.2.1).sum ≤ 1 := by
      decide
    exact key e (hmem e (by simp)) f (hmem f (by simp)) hsub hw
  | _ :: _ :: _ :: _, _, _, hlen, _, _ => simp at hlen

/-- No-instance: well formed, but budget `1` cannot keep the path connected. -/
example : diameterSpanningSubgraphDec (bitEncode (path3 1 1 2)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => path3_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: the weight `0` is rejected, although both edges then fit the budget `1`. -/
example : diameterSpanningSubgraphDec (bitEncode (path3 0 1 2)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed endpoints
  decide

example : DiameterSpanningSubgraphFeasible (path3 0 1 2) := path3_feasible 0 1 le_rfl

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := DiameterSpanningSubgraphInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : diameterSpanningSubgraphDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph
