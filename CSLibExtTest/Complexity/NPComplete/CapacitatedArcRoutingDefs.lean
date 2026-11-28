/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CapacitatedArcRoutingDefs

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedArcRouting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Karp (edgeGraph)
open SimpleGraph

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : CapacitatedArcRoutingInstance) :
    capacitatedArcRoutingDec (bitEncode i) = true ↔
      WellFormed i ∧ CapacitatedArcRoutingFeasible i := by
  simp [capacitatedArcRoutingDec, bitDecode_bitEncode]

/-- One street `{0, 1}` of cost `1` and demand `d`, depot `0`, capacity `W`, cost bound `B`. -/
private abbrev street (d W B : ℕ) : CapacitatedArcRoutingInstance :=
  (2, [(0, 1, 1, d)], 0, W, B)

example : WellFormed (street 1 1 2) := by unfold WellFormed endpoints; decide

/-- The street is an edge of the graph, in both directions. -/
private theorem street_adj (d W B : ℕ) :
    (Graph (street d W B)).Adj 0 1 ∧ (Graph (street d W B)).Adj 1 0 := by
  simp [Graph, endpoints, edgeGraph]

/-- The round trip `0 → 1 → 0` from the depot. -/
private def roundTrip (d W B : ℕ) : (Graph (street d W B)).Walk 0 0 :=
  .cons (street_adj d W B).1 (.cons (street_adj d W B).2 .nil)

/-- Yes-instance: one vehicle drives `0 → 1 → 0`, serving demand `1 ≤ W` at cost `2 ≤ B`. -/
example : capacitatedArcRoutingDec (bitEncode (street 1 1 2)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed endpoints; decide, 0, rfl, 1,
    fun _ => roundTrip 1 1 2, fun _ => 0, fun e _ => ?_, fun k => ?_, ?_⟩
  · fin_cases e
    simp [roundTrip]
  · fin_cases k
    decide
  · simp [roundTrip, edgeCost]

/-- With capacity `2` the same round trip serves the street at demand `2`. -/
example : capacitatedArcRoutingDec (bitEncode (street 2 2 10)) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed endpoints; decide, 0, rfl, 1,
    fun _ => roundTrip 2 2 10, fun _ => 0, fun e _ => ?_, fun k => ?_, ?_⟩
  · fin_cases e
    simp [roundTrip]
  · fin_cases k
    decide
  · simp [roundTrip, edgeCost]

/-- A route serving the street at demand `2` exceeds the capacity `1`. -/
private theorem street_heavy_not_feasible : ¬ CapacitatedArcRoutingFeasible (street 2 1 10) := by
  rintro ⟨v₀, -, m, C, s, -, hW, -⟩
  have h := hW (s 0)
  have hf : Finset.univ.filter (fun e => s e = s 0) = {0} := by
    ext e
    have he : e = 0 := Fin.ext (Nat.lt_one_iff.1 e.isLt)
    simp [he]
  rw [hf, Finset.sum_singleton] at h
  exact absurd h (by decide)

/-- No-instance (capacity): well formed, but the demand `2` of the street exceeds the vehicle
capacity `1`, whatever the cost budget. -/
example : capacitatedArcRoutingDec (bitEncode (street 2 1 10)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => street_heavy_not_feasible ((dec_bitEncode _).1 h).2

/-- A closed walk at the depot that uses the street traverses it at least twice. -/
private theorem two_le_cost {d W B : ℕ} (p : (Graph (street d W B)).Walk 0 0)
    (hp : p.edges ≠ []) : 2 ≤ (p.edges.map (edgeCost (street d W B))).sum := by
  have hn0 : ∀ x : Fin 2, (Graph (street d W B)).Adj 0 x → x = 1 := by
    intro x hx; revert hx; fin_cases x <;> simp [Graph, endpoints, edgeGraph]
  have hn1 : ∀ x : Fin 2, (Graph (street d W B)).Adj 1 x → x = 0 := by
    intro x hx; revert hx; fin_cases x <;> simp [Graph, endpoints, edgeGraph]
  cases p with
  | nil => exact absurd rfl hp
  | cons h q =>
    obtain rfl := hn0 _ h
    cases q with
    | cons h' r =>
      obtain rfl := hn1 _ h'
      simp only [Walk.edges_cons, List.map_cons, List.sum_cons]
      have h01 : edgeCost (street d W B) s(0, 1) = 1 := by simp [edgeCost]
      have h10 : edgeCost (street d W B) s(1, 0) = 1 := by simp [edgeCost]
      omega

/-- Serving the street needs a round trip of cost `2 > 1`. -/
private theorem street_cheap_not_feasible : ¬ CapacitatedArcRoutingFeasible (street 1 1 1) := by
  rintro ⟨v₀, hv₀, m, C, s, hserve, -, hB⟩
  obtain rfl : v₀ = 0 := Fin.ext hv₀
  have hmem := hserve 0 (by decide)
  have hne : (C (s 0)).edges ≠ [] := by
    intro h
    rw [h] at hmem
    simp at hmem
  have h2 := two_le_cost (C (s 0)) hne
  have hle := Finset.add_sum_erase Finset.univ
    (fun k => ((C k).edges.map (edgeCost (street 1 1 1))).sum) (Finset.mem_univ (s 0))
  have : ∑ k, ((C k).edges.map (edgeCost (street 1 1 1))).sum ≤ 1 := hB
  simp only at hle
  omega

/-- No-instance (cost): well formed, but serving the street costs at least `2 > 1`. -/
example : capacitatedArcRoutingDec (bitEncode (street 1 1 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => street_cheap_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: a loop entry `(0, 0, 1, 0)` is rejected. -/
example : capacitatedArcRoutingDec
    (bitEncode ((2, [(0, 1, 1, 1), (0, 0, 1, 0)], 0, 1, 2) : CapacitatedArcRoutingInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed endpoints
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := CapacitatedArcRoutingInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : capacitatedArcRoutingDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.CapacitatedArcRouting
