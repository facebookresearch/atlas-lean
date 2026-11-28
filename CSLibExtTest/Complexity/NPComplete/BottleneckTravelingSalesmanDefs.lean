/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : BottleneckTravelingSalesmanInstance) :
    bottleneckTravelingSalesmanDec (bitEncode i) = true ↔
      WellFormed i ∧ BottleneckTravelingSalesmanFeasible i := by
  simp [bottleneckTravelingSalesmanDec, bitDecode_bitEncode]

/-- Three cities at mutual distance `1`, with bound `1`. -/
private abbrev unitTriangle : BottleneckTravelingSalesmanInstance :=
  (3, [[0, 1, 1], [1, 0, 1], [1, 1, 0]], 1)

/-- Three cities where `0` and `2` are at distance `2`, with bound `B`. -/
private abbrev longTriangle (B : ℕ) : BottleneckTravelingSalesmanInstance :=
  (3, [[0, 1, 2], [1, 0, 1], [2, 1, 0]], B)

example : WellFormed unitTriangle := by unfold WellFormed; decide

example : WellFormed (longTriangle 1) := by unfold WellFormed; decide

/-- Yes-instance: the tour `0, 1, 2` uses only edges of length `1`. -/
example : bottleneckTravelingSalesmanDec (bitEncode unitTriangle) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, [0, 1, 2], by decide, by decide⟩

/-- Raising the bound to `2` makes the long triangle feasible, with the tour `0, 1, 2`. -/
example : bottleneckTravelingSalesmanDec (bitEncode (longTriangle 2)) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, [0, 1, 2], by decide, by decide⟩

/-- Every tour of three cities uses the edge `{0, 2}` of length `2`. -/
private theorem longTriangle_one_not_feasible :
    ¬ BottleneckTravelingSalesmanFeasible (longTriangle 1) := by
  rintro ⟨tour, hp, h⟩
  have key : ∀ a < 3, ∀ b < 3, ∀ c < 3, [a, b, c].Perm (List.range 3) →
      ¬ ∀ j < 3, dist (longTriangle 1).2.1 ([a, b, c].getD j 0)
        ([a, b, c].getD ((j + 1) % 3) 0) ≤ 1 := by
    decide
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 (by simpa using hp.length_eq)
  have hm : ∀ x ∈ [a, b, c], x < 3 := fun x hx => List.mem_range.1 (hp.subset hx)
  exact key a (hm a (by simp)) b (hm b (by simp)) c (hm c (by simp)) hp h

/-- No-instance: well formed, but every tour has an edge longer than the bound `1`. -/
example : bottleneckTravelingSalesmanDec (bitEncode (longTriangle 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => longTriangle_one_not_feasible ((dec_bitEncode _).1 h).2

/-- Malformed: an asymmetric matrix is rejected although the tour `0, 1, 2` meets the bound. -/
example : bottleneckTravelingSalesmanDec
    (bitEncode ((3, [[0, 1, 1], [1, 0, 1], [2, 1, 0]], 2) : BottleneckTravelingSalesmanInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := BottleneckTravelingSalesmanInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : bottleneckTravelingSalesmanDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman
