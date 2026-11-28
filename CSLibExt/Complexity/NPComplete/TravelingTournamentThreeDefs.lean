/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING TOURNAMENT PROBLEM with maximum streak 3: definitions

Source:
C. Thielen and S. Westphal, "Complexity of the traveling tournament problem", Theoretical
Computer Science 412(4-5) (2011), 345-351, doi:10.1016/j.tcs.2010.10.001;
decision version (TTP-k) as restated in D. Chatterjee, "Complexity of traveling tournament
problem with trip length more than three", arXiv:2110.02300 (2021), Definition 1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnconstrainedTravelingTournamentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree

open UnconstrainedTravelingTournament (TravelingTournamentInstance numTeams distance WellFormed
  numRounds IsDoubleRoundRobin totalTravel)

/-- No team of the `n` teams plays 4 consecutive rounds with the same home/away status. -/
def AtMostThreeConsecutive (n : ℕ) (home : ℕ → ℕ → Bool) : Prop :=
  ∀ t < n, ∀ r, r + 3 < numRounds n →
    ¬ (home t r = home t (r + 1) ∧ home t (r + 1) = home t (r + 2) ∧
      home t (r + 2) = home t (r + 3))

/-- No team of the `n` teams plays the same opponent in two consecutive rounds. -/
def NoRepeaters (n : ℕ) (opp : ℕ → ℕ → ℕ) : Prop :=
  ∀ t < n, ∀ r, r + 1 < numRounds n → opp t r ≠ opp t (r + 1)

/-- Some double round robin schedule with at most 3 consecutive home or away matches and no
repeaters has total travel distance at most `K`. -/
def TravelingTournamentThreeFeasible (i : TravelingTournamentInstance) : Prop :=
  ∃ opp : ℕ → ℕ → ℕ, ∃ home : ℕ → ℕ → Bool, IsDoubleRoundRobin (numTeams i) opp home ∧
    AtMostThreeConsecutive (numTeams i) home ∧ NoRepeaters (numTeams i) opp ∧
    totalTravel (distance i) (numTeams i) opp home ≤ i.2

open Classical in
/-- TRAVELING TOURNAMENT PROBLEM with maximum streak 3 as a decision problem over bitstrings. -/
noncomputable def travelingTournamentThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TravelingTournamentInstance) x with
  | some i => decide (WellFormed i ∧ TravelingTournamentThreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree
