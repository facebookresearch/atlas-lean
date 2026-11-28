/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE DOMINATING SET; M.
Yannakakis and F. Gavril, "Edge dominating sets in graphs" (1980).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EdgeDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet

/-!
# EDGE DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` edges
dominates all edges: every edge shares an endpoint with an edge in the set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EDGE DOMINATING SET is NP-complete.** The EDGE DOMINATING SET decision problem belongs to
NP, and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), EDGE DOMINATING SET; M. Yannakakis and F. Gavril, "Edge
dominating sets in graphs" (1980). -/
public theorem_wanted edgeDominatingSet_npComplete :
    edgeDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet
