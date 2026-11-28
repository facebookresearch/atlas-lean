/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwoDefs

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance
  BottleneckTravelingSalesmanFeasible dist)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BottleneckTravelingSalesmanInstance) :
    bottleneckTravelingSalesmanDistancesOneTwoDec (bitEncode i) = true ↔
      WellFormed i ∧ BottleneckTravelingSalesmanFeasible i := by
  simp [bottleneckTravelingSalesmanDistancesOneTwoDec, bitDecode_bitEncode]

/-- Three cities where `0` and `2` are at distance `2` and the other pairs at distance `1`. -/
private abbrev oneTwoTriangle (B : ℕ) : BottleneckTravelingSalesmanInstance :=
  (3, [[0, 1, 2], [1, 0, 1], [2, 1, 0]], B)

/-- The same triangle with the distance `3` between `0` and `2`. -/
private abbrev threeTriangle : BottleneckTravelingSalesmanInstance :=
  (3, [[0, 1, 3], [1, 0, 1], [3, 1, 0]], 3)

/-- The triangle with distances `1` and `2` is well formed for the bounds `1` and `2`. -/
private theorem oneTwoTriangle_wellFormed :
    WellFormed (oneTwoTriangle 1) ∧ WellFormed (oneTwoTriangle 2) := by
  unfold WellFormed BottleneckTravelingSalesman.WellFormed
  exact ⟨by decide, by decide⟩

/-- Yes-instance: with bound `2` the tour `0, 1, 2` is feasible. -/
example : bottleneckTravelingSalesmanDistancesOneTwoDec (bitEncode (oneTwoTriangle 2)) = true :=
  (dec_bitEncode _).2 ⟨oneTwoTriangle_wellFormed.2, [0, 1, 2], by decide, by decide⟩

/-- Every tour of three cities uses the edge `{0, 2}` of length `2`. -/
private theorem oneTwoTriangle_one_not_feasible :
    ¬ BottleneckTravelingSalesmanFeasible (oneTwoTriangle 1) := by
  rintro ⟨tour, hp, h⟩
  have key : ∀ a < 3, ∀ b < 3, ∀ c < 3, [a, b, c].Perm (List.range 3) →
      ¬ ∀ j < 3, dist (oneTwoTriangle 1).2.1 ([a, b, c].getD j 0)
        ([a, b, c].getD ((j + 1) % 3) 0) ≤ 1 := by
    decide
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 (by simpa using hp.length_eq)
  have hm : ∀ x ∈ [a, b, c], x < 3 := fun x hx => List.mem_range.1 (hp.subset hx)
  exact key a (hm a (by simp)) b (hm b (by simp)) c (hm c (by simp)) hp h

/-- No-instance: well formed, but with bound `1` every tour has an edge of length `2`. -/
example : bottleneckTravelingSalesmanDistancesOneTwoDec (bitEncode (oneTwoTriangle 1)) =
    false := by
  rw [Bool.eq_false_iff]
  exact fun h => oneTwoTriangle_one_not_feasible ((dec_bitEncode _).1 h).2

/-- The distance-`3` triangle is a well-formed, feasible instance of the general problem. -/
example : BottleneckTravelingSalesman.WellFormed threeTriangle ∧
    BottleneckTravelingSalesmanFeasible threeTriangle :=
  ⟨by unfold BottleneckTravelingSalesman.WellFormed; decide, [0, 1, 2], by decide, by decide⟩

/-- Malformed for this restriction: the distance `3` is rejected, although the tour `0, 1, 2`
meets the bound `3`. -/
example : bottleneckTravelingSalesmanDistancesOneTwoDec (bitEncode threeTriangle) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed BottleneckTravelingSalesman.WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BottleneckTravelingSalesmanInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : bottleneckTravelingSalesmanDistancesOneTwoDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo
