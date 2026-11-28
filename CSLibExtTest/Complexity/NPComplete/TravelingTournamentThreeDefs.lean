/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TravelingTournamentThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree

open MetaMathlibExt.BitstringEncoding
open UnconstrainedTravelingTournament (TravelingTournamentInstance numTeams distance WellFormed
  numRounds IsDoubleRoundRobin totalTravel)

/-- Four teams, every two at distance `1`, with bound `17`. -/
private abbrev four : TravelingTournamentInstance :=
  ([[0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0]], 17)

private theorem four_wellFormed : WellFormed four := by
  unfold WellFormed distance numTeams
  exact ⟨by decide, ⟨2, rfl⟩, by decide, by decide, by decide, by decide⟩

/-- The opponents of a single round robin `{0-1, 2-3}`, `{0-2, 1-3}`, `{0-3, 1-2}`, played
twice. -/
private def opp4 (t r : ℕ) : ℕ := ([[1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]].getD (r % 3) []).getD t 0

/-- The first-listed team of each match hosts it in rounds `0, 1, 2` and travels in the mirrored
rounds `3, 4, 5`. -/
private def home4 (t r : ℕ) : Bool :=
  decide (r < 3) ==
    ([[true, false, true, false], [true, true, false, false], [true, true, false, false]].getD
      (r % 3) []).getD t false

private theorem four_schedule : IsDoubleRoundRobin 4 opp4 home4 := by
  unfold IsDoubleRoundRobin; decide

/-- Team `0`, for example, plays home, home, home, away, away, away: no streak of four. -/
private theorem four_streaks : AtMostThreeConsecutive 4 home4 := by
  have h : ∀ t < 4, ∀ r < 3,
      ¬ (home4 t r = home4 t (r + 1) ∧ home4 t (r + 1) = home4 t (r + 2) ∧
        home4 t (r + 2) = home4 t (r + 3)) := by decide
  intro t ht r hr
  change r + 3 < 6 at hr
  exact h t ht r (by omega)

/-- Round `2` (`0-3`) is followed by round `3` (`0-1`), and so on: no team meets the same
opponent twice in a row. -/
private theorem four_noRepeaters : NoRepeaters 4 opp4 := by
  have h : ∀ t < 4, ∀ r < 5, opp4 t r ≠ opp4 t (r + 1) := by decide
  intro t ht r hr
  change r + 1 < 6 at hr
  exact h t ht r (by omega)

private theorem four_travel : totalTravel (distance four) 4 opp4 home4 = 17 := by decide

private theorem four_feasible : TravelingTournamentThreeFeasible four :=
  ⟨opp4, home4, four_schedule, four_streaks, four_noRepeaters, four_travel.le⟩

/-- Two teams at distance `1`, with bound `4`. -/
private abbrev two : TravelingTournamentInstance := ([[0, 1], [1, 0]], 4)

private theorem two_wellFormed : WellFormed two := by
  unfold WellFormed distance numTeams
  exact ⟨by decide, ⟨1, rfl⟩, by decide, by decide, by decide, by decide⟩

/-- Two teams always meet in both rounds, which is a repeater: `two` is infeasible here. -/
private theorem two_infeasible : ¬ TravelingTournamentThreeFeasible two := by
  rintro ⟨opp, home, ⟨hm, -⟩, -, hrep, -⟩
  have h2 : numTeams two = 2 := rfl
  have o00 : opp 0 0 = 1 := by have := hm 0 (by decide) 0 (by decide); omega
  have o01 : opp 0 1 = 1 := by have := hm 0 (by decide) 1 (by decide); omega
  exact hrep 0 (by decide) 0 (by decide) (o00.trans o01.symm)

/-- `two` is feasible for the unconstrained problem: team `t` hosts round `t`, total travel
`4`. -/
private theorem two_unconstrained_feasible :
    UnconstrainedTravelingTournament.UnconstrainedTravelingTournamentFeasible two :=
  ⟨fun t _ => 1 - t, fun t r => decide (t = r), by unfold IsDoubleRoundRobin; decide,
    by decide⟩

/-- The decision problem accepts the encoding of `four`. -/
example : travelingTournamentThreeDec (bitEncode four) = true := by
  simp [travelingTournamentThreeDec, four_wellFormed, four_feasible]

/-- It rejects the encoding of the well-formed but infeasible `two`, which the unconstrained
problem accepts: only the no-repeater rule separates them. -/
example :
    UnconstrainedTravelingTournament.unconstrainedTravelingTournamentDec (bitEncode two) = true ∧
      travelingTournamentThreeDec (bitEncode two) = false :=
  ⟨by simp [UnconstrainedTravelingTournament.unconstrainedTravelingTournamentDec, two_wellFormed,
      two_unconstrained_feasible],
    by simp [travelingTournamentThreeDec, two_infeasible]⟩

/-- A team playing four home matches in a row breaks the streak rule. -/
example : ¬ AtMostThreeConsecutive 4 fun t r => decide (t = 0 ∧ r < 4) := by
  intro h
  exact h 0 (by decide) 0 (by decide) (by decide)

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : travelingTournamentThreeDec [true] = false := by
  have h : bitDecode (α := TravelingTournamentInstance) [true] = none := rfl
  simp [travelingTournamentThreeDec, h]

end MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree
