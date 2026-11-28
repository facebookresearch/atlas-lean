/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM INDUCED MATCHING is NP-complete

Source:
L. J. Stockmeyer and V. V. Vazirani, "NP-completeness of some generalizations of the maximum
matching problem", Information Processing Letters 15 (1982), 14-19; K. Cameron, "Induced
matchings", Discrete Applied Mathematics 24 (1989), 97-102 (NP-completeness for bipartite
graphs, polynomial for chordal graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumInducedMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching

/-!
# MAXIMUM INDUCED MATCHING is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has an induced matching
of at least `K` edges: a set of pairwise disjoint edges with no edge of the graph joining two
different matched edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM INDUCED MATCHING is NP-complete.** The MAXIMUM INDUCED MATCHING decision problem
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: L. J. Stockmeyer and V. V. Vazirani,
"NP-completeness of some generalizations of the maximum matching problem", Information
Processing Letters 15 (1982), 14-19; K. Cameron, "Induced matchings", Discrete Applied
Mathematics 24 (1989), 97-102 (NP-completeness for bipartite graphs, polynomial for
chordal graphs). -/
public theorem_wanted maximumInducedMatching_npComplete :
    maximumInducedMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumInducedMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching
