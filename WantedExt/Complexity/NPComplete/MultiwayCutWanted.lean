/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIWAY CUT; E. Dahlhaus
et al., "The complexity of multiterminal cuts" (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiwayCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayCut

/-!
# MULTIWAY CUT is NP-complete

An undirected graph, a list of terminals, and a bound `K`. The question is whether the
terminals can be pairwise separated by removing at most `K` edges, witnessed by an assignment
of every vertex to one terminal's part, sending each terminal to its own part, with at most `K`
cut edges, stated by forbidding `K + 1` cut edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIWAY CUT is NP-complete.** Let MULTIWAY CUT be the decision problem that accepts exactly
the bitstrings decoding to a well-formed, feasible multiway cut instance: a simple undirected graph
on the vertices $0, \dots, n-1$, a list of distinct terminal vertices and a bound $K$ such that
deleting at most $K$ edges of the graph leaves no two terminals connected. Then MULTIWAY CUT is in
NP, and every decision problem in NP reduces to MULTIWAY CUT by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MULTIWAY CUT; E. Dahlhaus et al., "The complexity of multiterminal
cuts" (1994). -/
public theorem_wanted multiwayCut_npComplete :
    multiwayCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayCutDec

end MetaMathlibExt.Complexity.NPComplete.MultiwayCut
