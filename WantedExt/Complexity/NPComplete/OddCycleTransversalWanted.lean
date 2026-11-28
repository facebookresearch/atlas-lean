/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ODD CYCLE TRANSVERSAL is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL
(vertex deletion to a bipartite graph).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OddCycleTransversalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal

/-!
# ODD CYCLE TRANSVERSAL is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` vertices can be
removed to make the graph bipartite, witnessed by a two-coloring of the remaining vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ODD CYCLE TRANSVERSAL is NP-complete.** The decision problem ODD CYCLE TRANSVERSAL, which
accepts a bitstring exactly when it decodes to a well-formed instance $(n, es, K)$ whose graph
becomes bipartite after removing some set of at most $K$ vertices, belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL (vertex deletion to a
bipartite graph). -/
public theorem_wanted oddCycleTransversal_npComplete :
    oddCycleTransversalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oddCycleTransversalDec

end MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal
