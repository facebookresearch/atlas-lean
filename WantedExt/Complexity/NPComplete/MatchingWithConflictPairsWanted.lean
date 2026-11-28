/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING WITH CONFLICT PAIRS is NP-complete

Source:
A. Darmann, U. Pferschy, J. Schauer and G. J. Woeginger, "Paths, trees and matchings under
disjunctive constraints", Discrete Applied Mathematics 159 (2011), 1726-1735,
doi:10.1016/j.dam.2010.12.016.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MatchingWithConflictPairsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatchingWithConflictPairs

/-!
# MATCHING WITH CONFLICT PAIRS is NP-complete

The maximum matching problem under negative disjunctive constraints of Darmann, Pferschy,
Schauer and Woeginger (2011), in decision form. An instance is a graph `G = (V, E)`, a set of
conflict pairs of edges of `G` (a negative disjunctive constraint states that the two edges of
a pair cannot be contained simultaneously in a feasible solution; the pairs are the edges of
the conflict graph on `E`), and an integer `K`. The question is whether `G` has a matching with
at least `K` edges that contains no conflict pair.

Darmann et al. prove that the maximum matching problem is NP-hard already for conflict graphs
in which every connected component is a single edge; the stated problem allows any conflict
graph, so it contains that class. NP membership is immediate (a matching is a polynomial-size
certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MATCHING WITH CONFLICT PAIRS is NP-complete.** Source: Darmann, Pferschy, Schauer and
Woeginger (2011). -/
public theorem_wanted matchingWithConflictPairs_npComplete :
    matchingWithConflictPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matchingWithConflictPairsDec

end MetaMathlibExt.Complexity.NPComplete.MatchingWithConflictPairs
