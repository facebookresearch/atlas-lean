/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM: definitions

Source:
R. Bhattacharyya, "Complexity of the unconstrained traveling tournament problem", Operations
Research Letters 44(5) (2016), 649-654, doi:10.1016/j.orl.2016.07.011, Theorem 1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even

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
