/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED PATH COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PATH COVER (the `K = 1`
slice is Hamiltonian path).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedPathCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedPathCover

/-!
# DIRECTED PATH COVER is NP-complete

A directed graph and a bound `K`. The question is whether all vertices can be covered by at
most `K` directed paths: simple vertex-disjoint paths (singleton paths allowed) whose vertex
sets partition the vertex set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED PATH COVER is NP-complete.** The decision problem DIRECTED PATH COVER is in NP,
and every decision problem in NP has a polynomial-time many-one reduction to
DIRECTED PATH COVER.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), PATH COVER (the `K = 1` slice is Hamiltonian path). -/
public theorem_wanted directedPathCover_npComplete :
    directedPathCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedPathCoverDec

end MetaMathlibExt.Complexity.NPComplete.DirectedPathCover
