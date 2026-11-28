/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE COLORING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE COLORING; I. Holyer,
"The NP-completeness of edge-coloring" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeColoring

/-!
# EDGE COLORING is NP-complete

An undirected graph and a bound `K`. The question is whether the chromatic index is at most
`K`: a coloring of the edges with colors `0, …, K - 1` in which edges sharing an endpoint
differ.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EDGE COLORING is NP-complete.** The EDGE COLORING decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), EDGE COLORING; I. Holyer, "The NP-completeness of edge-coloring"
(1981). -/
public theorem_wanted edgeColoring_npComplete :
    edgeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeColoringDec

end MetaMathlibExt.Complexity.NPComplete.EdgeColoring
