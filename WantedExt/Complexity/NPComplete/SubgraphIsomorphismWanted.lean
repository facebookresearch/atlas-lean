/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SUBGRAPH ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SubgraphIsomorphismDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism

/-!
# SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is a (not
necessarily induced) subgraph of `G`: an injective map from the vertices of `H` to those of `G`
sending every edge of `H` to an edge of `G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SUBGRAPH ISOMORPHISM is NP-complete.** The decision problem SUBGRAPH ISOMORPHISM belongs
to NP, and every decision problem $L$ in NP has a polynomial-time many-one reduction to
SUBGRAPH ISOMORPHISM.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), SUBGRAPH ISOMORPHISM. -/
public theorem_wanted subgraphIsomorphism_npComplete :
    subgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
