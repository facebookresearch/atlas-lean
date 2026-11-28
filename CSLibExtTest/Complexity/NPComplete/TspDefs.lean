/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TspDefs

namespace MetaMathlibExt.Complexity.NPComplete.Tsp

open MetaMathlibExt.BitstringEncoding

/-- Four cities on a unit square: adjacent corners at distance `1`, opposite corners at
distance `2`. -/
private abbrev square : List (List ℕ) :=
  [[0, 1, 2, 1], [1, 0, 1, 2], [2, 1, 0, 1], [1, 2, 1, 0]]

private theorem square_wellFormed (B : ℕ) : WellFormed (4, square, B) := by
  unfold WellFormed; dsimp only; decide

/-- Going around the square, `0, 1, 2, 3`, has length `4`. -/
example : TourLength square [0, 1, 2, 3] = 4 := by decide

/-- Crossing the square, `0, 2, 1, 3`, has length `6`: the order of the cities matters. -/
example : TourLength square [0, 2, 1, 3] = 6 := by decide

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

/-- A tour must visit every city: `0, 1` alone is short enough but misses `2` and `3`. -/
example : TourLength square [0, 1] ≤ 3 ∧ ¬ ∀ v < 4, v ∈ [0, 1] := by decide

/-- An asymmetric matrix is malformed, although the tour `0, 1` has length `1 + 5 ≤ 6`. -/
private theorem asym_malformed : ¬ WellFormed (2, [[0, 1], [5, 0]], 6) := by
  unfold WellFormed; decide

private theorem asym_feasible : TspFeasible (2, [[0, 1], [5, 0]], 6) :=
  ⟨[0, 1], by decide, rfl, by decide, by decide⟩

/-- The decision problem accepts the encoding of the square with bound `4`. -/
example : tspDec (bitEncode ((4, square, 4) : TspInstance)) = true := by
  simp [tspDec, square_wellFormed, square_four_feasible]

/-- It rejects the encoding of the well-formed square with bound `3`. -/
example : tspDec (bitEncode ((4, square, 3) : TspInstance)) = false := by
  simp [tspDec, square_three_infeasible]

/-- It rejects the asymmetric instance, which is feasible but malformed. -/
example : TspFeasible (2, [[0, 1], [5, 0]], 6) ∧
    tspDec (bitEncode ((2, [[0, 1], [5, 0]], 6) : TspInstance)) = false :=
  ⟨asym_feasible, by simp [tspDec, asym_malformed]⟩

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : tspDec [true] = false := by
  have h : bitDecode (α := TspInstance) [true] = none := rfl
  simp [tspDec, h]

end MetaMathlibExt.Complexity.NPComplete.Tsp
