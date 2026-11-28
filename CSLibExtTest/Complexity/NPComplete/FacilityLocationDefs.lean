/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FacilityLocationDefs

namespace MetaMathlibExt.Complexity.NPComplete.FacilityLocation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem le_sum_of_mem {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.sum
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

/-- Facilities with opening costs `1, 5`; clients with assignment costs `(1, 3)` and `(2, 3)`. -/
private abbrev yes : FacilityLocationInstance := ([1, 5], [[1, 3], [2, 3]], 4)

/-- The same facilities and clients with budget `3`; the cheapest plan costs `4`. -/
private abbrev no : FacilityLocationInstance := ([1, 5], [[1, 3], [2, 3]], 3)

/-- The decision problem accepts `yes`: open facility `0` and assign both clients to it, at cost
`1 + 1 + 2 = 4`. -/
example : facilityLocationDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : FacilityLocationFeasible yes := by
    refine ⟨[0, 0], rfl, by decide, [0], by decide, ?_, by decide, by decide⟩
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    exact ⟨0, by decide, by simp [hf]⟩
  simp [facilityLocationDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`: the facility of client `0` is
open, so every plan costs at least its opening cost plus both assignment costs, and that is at
least `4`. -/
example : WellFormed no ∧ facilityLocationDec (bitEncode no) = false := by
  have hf : ¬ FacilityLocationFeasible no := by
    rintro ⟨assign, -, hrange, used, -, -, hused, hcost⟩
    have h0 := hrange 0 (by decide)
    have h1 := hrange 1 (by decide)
    have hopen : [1, 5].getD (assign.getD 0 0) 0 ≤ (used.map fun f => [1, 5].getD f 0).sum :=
      le_sum_of_mem (List.mem_map.2 ⟨_, hused 0 (by decide), rfl⟩)
    simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
      Finset.sum_range_zero] at hcost
    have key : ∀ a < 2, ∀ b < 2,
        3 < [1, 5].getD a 0 + ([[1, 3], [2, 3]].getD 0 []).getD a 0 +
          ([[1, 3], [2, 3]].getD 1 []).getD b 0 := by decide
    have := key _ h0 _ h1
    omega
  exact ⟨by unfold WellFormed; decide, by simp [facilityLocationDec, bitDecode_bitEncode, hf]⟩

/-- The row `(0, 9)` has two entries for one facility, so the instance is malformed, although assigning the client to facility `0` costs only `1`. -/
example :
    FacilityLocationFeasible (([1], [[0, 9]], 1) : FacilityLocationInstance) ∧
      facilityLocationDec (bitEncode (([1], [[0, 9]], 1) : FacilityLocationInstance)) = false := by
  have hw : ¬ WellFormed (([1], [[0, 9]], 1) : FacilityLocationInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨[0], rfl, by decide, [0], by decide, ?_, by decide, by decide⟩,
    by simp [facilityLocationDec, bitDecode_bitEncode, hw]⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  exact ⟨0, by decide, by simp [hf]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : facilityLocationDec [true] = false := by
  have h : bitDecode (α := FacilityLocationInstance) [true] = none := rfl
  simp [facilityLocationDec, h]

end MetaMathlibExt.Complexity.NPComplete.FacilityLocation
