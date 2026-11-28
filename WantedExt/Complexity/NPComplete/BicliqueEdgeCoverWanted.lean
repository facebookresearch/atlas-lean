/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLIQUE EDGE COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BICLIQUE COVER.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BicliqueEdgeCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover

/-!
# BICLIQUE EDGE COVER is NP-complete

A bipartite graph (left vertices `0, …, L - 1`, right vertices `0, …, R - 1`) and a bound `K`.
The question is whether all edges can be covered by at most `K` complete bipartite subgraphs
(bicliques), each given by a left set and a right set with all cross pairs present as edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BICLIQUE EDGE COVER is NP-complete.** The biclique edge cover decision problem belongs to
NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), BICLIQUE COVER. -/
public theorem_wanted bicliqueEdgeCover_npComplete :
    bicliqueEdgeCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bicliqueEdgeCoverDec

end MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover
