/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even

/-!
# UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM: definitions

INSTANCE: an even number `n` of teams, an `n × n` matrix `D` of distances between their home
venues, and an integer `K`.
QUESTION: is there a double round robin league schedule of the `n` teams with total distance
traveled by all the teams at most `K`?

A double round robin league schedule has `2(n - 1)` rounds; in every round each team plays
exactly one match, at home or away, and each team plays every other team twice, once at home
and once away. No bound is put on the number of consecutive home or away matches (that is what
"unconstrained" means). Each team starts at its home venue, travels to the venue of each of its
matches in turn (the home venue of the team it plays away), and returns home after the last
round; the total distance is the sum over all teams. Bhattacharyya assumes without loss of
generality that `D` is a metric; `WellFormed` requires `D` symmetric with zero diagonal and
satisfying the triangle inequality, and allows distance `0` between distinct teams, because his
reduction from (1,2)-TSP places many teams at the same vertex ("(m + 1)(10m + 9) teams are
placed at vertex u"). Distances and `K` are natural numbers; binary encoding.

A schedule is given by `opp t r`, the opponent of team `t` in round `r`, and `home t r`, whether
`t` plays at home in round `r` (teams `0, …, n - 1`, rounds `0, …, 2n - 3`).
`IsDoubleRoundRobin` and `totalTravel` are stated for any distance function, for reuse by
other traveling tournament variants.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
R. Bhattacharyya, "Complexity of the unconstrained traveling tournament problem", Operations
Research Letters 44(5) (2016), 649-654, doi:10.1016/j.orl.2016.07.011, Theorem 1.1.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament

/-- An instance: the distance matrix row by row (`D_ab` is entry `b` of row `a`; one row per
team), and the bound `K`. -/
abbrev TravelingTournamentInstance := List (List ℕ) × ℕ

/-- The number of teams: one per row of the distance matrix. -/
abbrev numTeams (i : TravelingTournamentInstance) : ℕ := i.1.length

/-- The distance `D_ab` between the home venues of teams `a` and `b`. -/
def distance (i : TravelingTournamentInstance) (a b : ℕ) : ℕ := (i.1.getD a []).getD b 0

/-- Well-formedness of an instance: an even number `n ≥ 2` of teams, an `n × n` distance matrix,
zero diagonal, symmetry and the triangle inequality. -/
def WellFormed (i : TravelingTournamentInstance) : Prop :=
  2 ≤ numTeams i ∧ Even (numTeams i) ∧ (∀ row ∈ i.1, row.length = numTeams i) ∧
    (∀ a < numTeams i, distance i a a = 0) ∧
    (∀ a < numTeams i, ∀ b < numTeams i, distance i a b = distance i b a) ∧
    ∀ a < numTeams i, ∀ b < numTeams i, ∀ c < numTeams i,
      distance i a c ≤ distance i a b + distance i b c

/-- The number of rounds of a double round robin schedule of `n` teams, `2(n - 1)`. -/
abbrev numRounds (n : ℕ) : ℕ := 2 * (n - 1)

/-- `opp` and `home` form a double round robin league schedule of `n` teams: in every round each
team `t` plays a match against another team `opp t r`, who plays `t` in that round with the
opposite home/away status, and for any two distinct teams `a` and `b` there is exactly one round
in which `a` plays `b` at home. -/
def IsDoubleRoundRobin (n : ℕ) (opp : ℕ → ℕ → ℕ) (home : ℕ → ℕ → Bool) : Prop :=
  (∀ t < n, ∀ r < numRounds n, opp t r < n ∧ opp t r ≠ t ∧ opp (opp t r) r = t ∧
    home (opp t r) r = !home t r) ∧
  ∀ a < n, ∀ b < n, a ≠ b →
    ((Finset.range (numRounds n)).filter fun r => opp a r = b ∧ home a r = true).card = 1

/-- The venue of team `t`'s match in round `r`: its own home venue, or that of its opponent. -/
def venue (opp : ℕ → ℕ → ℕ) (home : ℕ → ℕ → Bool) (t r : ℕ) : ℕ :=
  if home t r then t else opp t r

/-- The total distance traveled by the `n` teams under distances `d`: each team goes from home to
its first venue, from each venue to the next, and from its last venue back home. -/
def totalTravel (d : ℕ → ℕ → ℕ) (n : ℕ) (opp : ℕ → ℕ → ℕ) (home : ℕ → ℕ → Bool) : ℕ :=
  ∑ t ∈ Finset.range n,
    (d t (venue opp home t 0) +
      (∑ r ∈ Finset.range (numRounds n - 1),
        d (venue opp home t r) (venue opp home t (r + 1))) +
      d (venue opp home t (numRounds n - 1)) t)

/-- Some double round robin league schedule has total travel distance at most `K`. -/
def UnconstrainedTravelingTournamentFeasible (i : TravelingTournamentInstance) : Prop :=
  ∃ opp : ℕ → ℕ → ℕ, ∃ home : ℕ → ℕ → Bool, IsDoubleRoundRobin (numTeams i) opp home ∧
    totalTravel (distance i) (numTeams i) opp home ≤ i.2

open Classical in
/-- UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM as a decision problem over bitstrings. -/
noncomputable def unconstrainedTravelingTournamentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TravelingTournamentInstance) x with
  | some i => decide (WellFormed i ∧ UnconstrainedTravelingTournamentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament
