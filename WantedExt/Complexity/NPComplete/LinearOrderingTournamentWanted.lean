/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR ORDERING (TOURNAMENTS) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LINEAR ORDERING; N. Alon,
"Ranking tournaments" (2006) and the feedback arc set literature.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LinearOrderingTournamentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearOrderingTournament

/-!
# LINEAR ORDERING (TOURNAMENTS) is NP-complete

A tournament (for every distinct pair of vertices exactly one direction is an edge) and a bound
`K`. The question is whether some vertex ordering has at least `K` forward arcs, witnessed by a
sublist of at least `K` forward edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LINEAR ORDERING (TOURNAMENTS) is NP-complete.** The decision problem LINEAR ORDERING
(TOURNAMENTS) on bitstrings lies in NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), LINEAR ORDERING; N. Alon, "Ranking tournaments"
(2006) and the feedback arc set literature. -/
public theorem_wanted linearOrderingTournament_npComplete :
    linearOrderingTournamentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearOrderingTournamentDec

end MetaMathlibExt.Complexity.NPComplete.LinearOrderingTournament
