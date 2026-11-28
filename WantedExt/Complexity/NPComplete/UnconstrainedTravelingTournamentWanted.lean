/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM is NP-complete

Source:
R. Bhattacharyya, "Complexity of the unconstrained traveling tournament problem", Operations
Research Letters 44(5) (2016), 649-654, doi:10.1016/j.orl.2016.07.011, Theorem 1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnconstrainedTravelingTournamentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament

/-!
# UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM is NP-complete

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

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNCONSTRAINED TRAVELING TOURNAMENT PROBLEM is NP-complete.** NP-hardness: Bhattacharyya
(2016), Theorem 1.1. Membership in NP: a schedule (`2(n - 1)` rounds of `n` opponents and
home/away flags) is a certificate of polynomial size whose conditions and total travel distance
are checked in polynomial time. -/
public theorem_wanted unconstrainedTravelingTournament_npComplete :
    unconstrainedTravelingTournamentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unconstrainedTravelingTournamentDec

end MetaMathlibExt.Complexity.NPComplete.UnconstrainedTravelingTournament
