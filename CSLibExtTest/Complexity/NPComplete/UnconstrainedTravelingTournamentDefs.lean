/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnconstrainedTravelingTournamentDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament

open MetaMathlibExt.BitstringEncoding

/-- Two teams at distance `1`, with bound `K`. -/
private abbrev two (K : ℕ) : TravelingTournamentInstance := ([[0, 1], [1, 0]], K)

private theorem two_wellFormed (K : ℕ) : WellFormed (two K) := by
  unfold WellFormed distance numTeams
  dsimp only
  exact ⟨by decide, ⟨1, rfl⟩, by decide, by decide, by decide, by decide⟩

/-- Each team plays the other in both rounds; team `t` is at home in round `t`. -/
private def opp2 (t _ : ℕ) : ℕ := 1 - t

private def home2 (t r : ℕ) : Bool := decide (t = r)

private theorem two_schedule : IsDoubleRoundRobin 2 opp2 home2 := by
  unfold IsDoubleRoundRobin; decide

/-- Each team travels `0 + 1 + 1` (home first) or `1 + 1 + 0` (away first): `4` in total. -/
private theorem two_travel : totalTravel (distance (two 4)) 2 opp2 home2 = 4 := by decide

private theorem two_four_feasible : UnconstrainedTravelingTournamentFeasible (two 4) :=
  ⟨opp2, home2, two_schedule, two_travel.le⟩

/-- Every double round robin schedule of two teams travels `4`: the opponent is forced, and
each team plays one home and one away match. -/
private theorem two_any_travel (K : ℕ) (opp : ℕ → ℕ → ℕ) (home : ℕ → ℕ → Bool)
    (h : IsDoubleRoundRobin 2 opp home) : totalTravel (distance (two K)) 2 opp home = 4 := by
  obtain ⟨hm, hc⟩ := h
  have o00 : opp 0 0 = 1 := by have := hm 0 (by decide) 0 (by decide); omega
  have o01 : opp 0 1 = 1 := by have := hm 0 (by decide) 1 (by decide); omega
  have o10 : opp 1 0 = 0 := by have := hm 1 (by decide) 0 (by decide); omega
  have o11 : opp 1 1 = 0 := by have := hm 1 (by decide) 1 (by decide); omega
  have h10 : home 1 0 = !home 0 0 := by
    have := (hm 0 (by decide) 0 (by decide)).2.2.2; rwa [o00] at this
  have h11 : home 1 1 = !home 0 1 := by
    have := (hm 0 (by decide) 1 (by decide)).2.2.2; rwa [o01] at this
  have hcount := hc 0 (by decide) 1 (by decide) (by decide)
  rw [Finset.card_filter] at hcount
  simp only [numRounds, Finset.sum_range_succ, Finset.sum_range_zero, o00, o01] at hcount
  simp only [totalTravel, numRounds, Finset.sum_range_succ, Finset.sum_range_zero, venue,
    o00, o01, o10, o11, h10, h11]
  cases h00 : home 0 0 <;> cases h01 : home 0 1 <;> simp [distance, h00, h01] at hcount ⊢

/-- With bound `3` the two teams are infeasible, as every schedule travels `4`. -/
private theorem two_three_infeasible : ¬ UnconstrainedTravelingTournamentFeasible (two 3) := by
  rintro ⟨opp, home, hs, hle⟩
  have h := two_any_travel 3 opp home hs
  change totalTravel (distance (two 3)) 2 opp home ≤ 3 at hle
  omega

/-- An odd number of teams is malformed. -/
example : ¬ WellFormed ([[0, 1, 1], [1, 0, 1], [1, 1, 0]], 10) := by
  unfold WellFormed distance
  intro ⟨_, ⟨k, hk⟩, _⟩
  change 3 = k + k at hk
  omega

/-- Distances violating the triangle inequality are malformed. -/
example : ¬ WellFormed ([[0, 1, 5, 1], [1, 0, 1, 1], [5, 1, 0, 1], [1, 1, 1, 0]], 100) := by
  unfold WellFormed distance
  intro ⟨_, _, _, _, _, h⟩
  exact absurd (h 0 (by decide) 1 (by decide) 2 (by decide)) (by decide)

/-- A schedule in which a team plays itself is not a double round robin. -/
example : ¬ IsDoubleRoundRobin 2 (fun t _ => t) home2 := by
  unfold IsDoubleRoundRobin; decide

/-- The decision problem accepts the encoding of `two 4`. -/
example : unconstrainedTravelingTournamentDec (bitEncode (two 4)) = true := by
  simp [unconstrainedTravelingTournamentDec, two_wellFormed, two_four_feasible]

/-- It rejects the encoding of the well-formed but infeasible `two 3`. -/
example : unconstrainedTravelingTournamentDec (bitEncode (two 3)) = false := by
  simp [unconstrainedTravelingTournamentDec, two_three_infeasible]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : unconstrainedTravelingTournamentDec [true] = false := by
  have h : bitDecode (α := TravelingTournamentInstance) [true] = none := rfl
  simp [unconstrainedTravelingTournamentDec, h]

end MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament
