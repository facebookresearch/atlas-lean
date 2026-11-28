/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RectilinearTravelingSalesmanDefs

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman

open MetaMathlibExt.BitstringEncoding
open GeometricTravelingSalesman (GeometricTravelingSalesmanInstance WellFormed)
open Tsp (TspFeasible TourLength)

/-- The corners `(0, 0)`, `(1, 0)`, `(1, 1)`, `(0, 1)` of the unit square, each coordinate
`p - q` written as the pair `(p, q)`, with the bound `B`. -/
private abbrev unitSquare (B : ℕ) : GeometricTravelingSalesmanInstance :=
  ([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((1, 0), (1, 0)), ((0, 0), (1, 0))], B)

/-- The `L₁` distance matrix of the square: adjacent corners at `1`, opposite corners at `2`. -/
private abbrev square : List (List ℕ) :=
  [[0, 1, 2, 1], [1, 0, 1, 2], [2, 1, 0, 1], [1, 2, 1, 0]]

private theorem toTsp_four : toTspInstance (unitSquare 4) = (4, square, 4) := by decide

private theorem toTsp_three : toTspInstance (unitSquare 3) = (4, square, 3) := by decide

/-- Opposite corners are at `L₁` distance `2`, not the Euclidean `√2`. -/
example : rectilinearDist (0, 0) (1, 1) = 2 := by decide

/-- Negative coordinates count by absolute value. -/
example : rectilinearDist (-2, 3) (1, -1) = 7 := by decide

private theorem unitSquare_wellFormed (B : ℕ) (hB : 0 < B) : WellFormed (unitSquare B) := by
  unfold WellFormed
  dsimp only
  exact ⟨by decide, by decide, hB⟩

/-- Going around the square, `0, 1, 2, 3`, has `L₁` length `4`. -/
private theorem unitSquare_four_feasible : RectilinearTravelingSalesmanFeasible (unitSquare 4) := by
  unfold RectilinearTravelingSalesmanFeasible
  rw [toTsp_four]
  exact ⟨[0, 1, 2, 3], by decide, rfl, by decide, by decide⟩

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

/-- Every tour of the square has `L₁` length at least `4`, so the bound `3` is not met. -/
private theorem unitSquare_three_infeasible :
    ¬ RectilinearTravelingSalesmanFeasible (unitSquare 3) := by
  unfold RectilinearTravelingSalesmanFeasible
  rw [toTsp_three]
  rintro ⟨tour, hnd, hlen, hall, hle⟩
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := tour_four hlen hall hnd
  have key : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4, [a, b, c, d].Nodup →
      3 < TourLength square [a, b, c, d] := by decide
  exact absurd hle (Nat.not_le.mpr (key a ha b hb c hc d hd hnd))

/-- The pairs `(1, 0)` and `(2, 1)` both encode the integer `1`, so this instance repeats the
point `(1, 0)` and is malformed; its two-point tour still meets the bound. -/
private abbrev repeated : GeometricTravelingSalesmanInstance :=
  ([((1, 0), (0, 0)), ((2, 1), (0, 0))], 1)

private theorem repeated_malformed : ¬ WellFormed repeated := by
  unfold WellFormed; decide

private theorem repeated_feasible : RectilinearTravelingSalesmanFeasible repeated :=
  ⟨[0, 1], by decide, by decide, by decide, by decide⟩

/-- The decision problem accepts the encoding of the square with bound `4`. -/
example : rectilinearTravelingSalesmanDec (bitEncode (unitSquare 4)) = true := by
  simp [rectilinearTravelingSalesmanDec, unitSquare_wellFormed 4 (by decide),
    unitSquare_four_feasible]

/-- It rejects the encoding of the well-formed square with bound `3`. -/
example : rectilinearTravelingSalesmanDec (bitEncode (unitSquare 3)) = false := by
  simp [rectilinearTravelingSalesmanDec, unitSquare_three_infeasible]

/-- It rejects the instance with a repeated point, which is feasible. -/
example : RectilinearTravelingSalesmanFeasible repeated ∧
    rectilinearTravelingSalesmanDec (bitEncode repeated) = false :=
  ⟨repeated_feasible, by simp [rectilinearTravelingSalesmanDec, repeated_malformed]⟩

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : rectilinearTravelingSalesmanDec [true] = false := by
  have h : bitDecode (α := GeometricTravelingSalesmanInstance) [true] = none := rfl
  simp [rectilinearTravelingSalesmanDec, h]

end MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman
