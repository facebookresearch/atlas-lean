/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING TOURNAMENT PROBLEM with maximum streak 3 is NP-complete

Source:
C. Thielen and S. Westphal, "Complexity of the traveling tournament problem", Theoretical
Computer Science 412(4-5) (2011), 345-351, doi:10.1016/j.tcs.2010.10.001;
decision version (TTP-k) as restated in D. Chatterjee, "Complexity of traveling tournament
problem with trip length more than three", arXiv:2110.02300 (2021), Definition 1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TravelingTournamentThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree

open UnconstrainedTravelingTournament (TravelingTournamentInstance numTeams distance WellFormed
  numRounds IsDoubleRoundRobin totalTravel)

/-!
# TRAVELING TOURNAMENT PROBLEM with maximum streak 3 is NP-complete

INSTANCE: an even number `n` of teams, an `n × n` matrix `D` of distances between their home
venues (symmetric, zero diagonal, triangle inequality), and an integer `K`.
QUESTION: is there a double round robin schedule (every two teams play twice, once at each of
their venues, and each team plays one match per round) in which no team plays more than 3
consecutive home or more than 3 consecutive away matches and no team plays the same opponent in
two consecutive rounds, with total travel distance at most `K`?

This is TTP(3) (TTP-k with `k = 3`). The instance, its well-formedness (even `n ≥ 2`, an `n × n`
matrix with zero diagonal, symmetric and satisfying the triangle inequality; distinct teams may
share a venue at distance `0`, as in Chatterjee's TTP-k reduction, which places "one or more
teams" at each vertex), the double round robin schedule with `2(n - 1)` rounds and the total
travel distance (each team starts at home, visits the venue of each of its matches in turn, and
returns home after the last round) are those of `UnconstrainedTravelingTournamentWanted`; this
module adds the two constraints: at most 3 consecutive home or away matches (no 4 consecutive
rounds with the same home/away status), and no repeaters (`opp t r ≠ opp t (r + 1)`), as in
Chatterjee's Definition 1.1 of TTP-k. Thielen and Westphal show that TTP(3) is NP-complete by a
reduction from 3-SAT; distances and `K` are natural numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRAVELING TOURNAMENT PROBLEM with maximum streak 3 is NP-complete.** NP-hardness: Thielen
and Westphal (2011). Membership in NP: the schedule is a certificate of polynomial size, checked in
polynomial time (Chatterjee (2021), Lemma 2.2, for TTP-k). -/
public theorem_wanted travelingTournamentThree_npComplete :
    travelingTournamentThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L travelingTournamentThreeDec

end MetaMathlibExt.Complexity.NPComplete.TravelingTournamentThree
