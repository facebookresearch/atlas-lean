/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TravelingSalesmanDistancesOneTwoDefs

namespace MetaMathlibExt.Complexity.NPComplete.TravelingSalesmanDistancesOneTwo

open MetaMathlibExt.BitstringEncoding
open Tsp (TspInstance TspFeasible TourLength)

/-- Four cities on a unit square: adjacent corners at distance `1`, opposite corners at
distance `2`. -/
private abbrev square : List (List ℕ) :=
  [[0, 1, 2, 1], [1, 0, 1, 2], [2, 1, 0, 1], [1, 2, 1, 0]]

private theorem square_wellFormed (B : ℕ) (hB : 0 < B) : WellFormed (4, square, B) := by
  unfold WellFormed Tsp.WellFormed
  dsimp only
  exact ⟨by decide, by decide, hB⟩

/-- The tour `0, 1, 2, 3` meets the bound `4`. -/
private theorem square_four_feasible : TspFeasible (4, square, 4) :=
  ⟨[0, 1, 2, 3], by decide, rfl, by decide, by decide⟩

/-- A tour of four cities is a list `[a, b, c, d]` of cities below `4`. -/
private theorem tour_four {tour : List ℕ} (hlen : tour.length = 4)
    (hall : ∀ v < 4, v ∈ tour) (hnd : tour.Nodup) :
    ∃ a < 4, ∃ b < 4, ∃ c < 4, ∃ d < 4, tour = [a, b, c, d] := by
  have hperm : (List.range 4).Perm tour :=
    (List.nodup_range.subperm fun v hv => hall v (List.mem_range.mp hv)).perm_of_length_le
      (by simp [hlen])
  have hlt : ∀ x ∈ tour, x < 4 := fun x hx => List.mem_range.mp (hperm.mem_iff.mpr hx)
  rcases tour with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨a, hlt a (by simp), b, hlt b (by simp), c, hlt c (by simp), d, hlt d (by simp), rfl⟩

/-- Every tour of the square has length at least `4`, so the bound `3` is not met. -/
private theorem square_three_infeasible : ¬ TspFeasible (4, square, 3) := by
  rintro ⟨tour, hnd, hlen, hall, hle⟩
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := tour_four hlen hall hnd
  have key : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4, [a, b, c, d].Nodup →
      3 < TourLength square [a, b, c, d] := by decide
  exact absurd hle (Nat.not_le.mpr (key a ha b hb c hc d hd hnd))

/-- The square with the diagonal `{0, 2}` stretched to `3`; still a symmetric matrix with zero
diagonal. -/
private abbrev stretched : List (List ℕ) :=
  [[0, 1, 3, 1], [1, 0, 1, 2], [3, 1, 0, 1], [1, 2, 1, 0]]

private theorem stretched_tspWellFormed : Tsp.WellFormed (4, stretched, 4) := by
  unfold Tsp.WellFormed; decide

private theorem stretched_feasible : TspFeasible (4, stretched, 4) :=
  ⟨[0, 1, 2, 3], by decide, rfl, by decide, by decide⟩

/-- The distance `3` is outside `{1, 2}`. -/
private theorem stretched_not_wellFormed : ¬ WellFormed (4, stretched, 4) := by
  unfold WellFormed Tsp.WellFormed; decide

/-- The bound `0` is malformed for this restriction. -/
example : ¬ WellFormed (4, square, 0) := by unfold WellFormed Tsp.WellFormed; decide

/-- The decision problem accepts the encoding of the square with bound `4`. -/
example : travelingSalesmanDistancesOneTwoDec (bitEncode ((4, square, 4) : TspInstance)) = true := by
  simp [travelingSalesmanDistancesOneTwoDec, square_wellFormed 4 (by decide), square_four_feasible]

/-- It rejects the encoding of the well-formed square with bound `3`. -/
example :
    travelingSalesmanDistancesOneTwoDec (bitEncode ((4, square, 3) : TspInstance)) = false := by
  simp [travelingSalesmanDistancesOneTwoDec, square_three_infeasible]

/-- The stretched square is accepted by TSP but rejected by the restriction to distances `1`
and `2`. -/
example :
    Tsp.tspDec (bitEncode ((4, stretched, 4) : TspInstance)) = true ∧
      travelingSalesmanDistancesOneTwoDec (bitEncode ((4, stretched, 4) : TspInstance)) =
        false := by
  refine ⟨?_, ?_⟩
  · simp [Tsp.tspDec, stretched_tspWellFormed, stretched_feasible]
  · simp [travelingSalesmanDistancesOneTwoDec, stretched_not_wellFormed]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : travelingSalesmanDistancesOneTwoDec [true] = false := by
  have h : bitDecode (α := TspInstance) [true] = none := rfl
  simp [travelingSalesmanDistancesOneTwoDec, h]

end MetaMathlibExt.Complexity.NPComplete.TravelingSalesmanDistancesOneTwo
