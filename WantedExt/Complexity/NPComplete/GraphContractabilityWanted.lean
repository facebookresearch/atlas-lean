/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH CONTRACTABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT51] GRAPH CONTRACTABILITY
(attributed there to R. Statman, unpublished, 1976);
A. E. Brouwer and H. J. Veldman, "Contractibility and NP-completeness", Journal of Graph
Theory 11 (1987), 71-79, doi:10.1002/jgt.3190110111.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphContractabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphContractability

/-!
# GRAPH CONTRACTABILITY is NP-complete

The name is Garey and Johnson's heading for [GT51]; the literature also spells it
"contractibility" (Brouwer and Veldman). Given graphs `G = (V₁, E₁)` and `H = (V₂, E₂)`, can a graph isomorphic to `H` be obtained
from `G` by a sequence of edge contractions, where each step replaces two adjacent vertices
`u, v` by a single vertex `w` adjacent to exactly those vertices that were previously adjacent
to at least one of `u` and `v`?

A sequence of edge contractions merges the vertices of `G` into classes, each class inducing a
connected subgraph of `G` (it is merged along edges), and the result is the quotient graph: two
classes are adjacent exactly when some edge of `G` joins them. Conversely, a partition of `V₁`
into classes inducing connected subgraphs is realized by contracting, class by class, the edges
of a spanning tree of each class. A graph isomorphic to `H` is obtained exactly when there is a
map `f : V₁ → V₂` whose fibers induce connected (in particular nonempty) subgraphs of `G` and
whose quotient `G.map f` (Mathlib's image graph: `x ≠ y` are adjacent when some edge of `G`
joins `f⁻¹ x` and `f⁻¹ y`) is `H`. The empty sequence is allowed, so `H ≅ G` is a
yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH CONTRACTABILITY is NP-complete.** Source: Garey and Johnson (1979), [GT51]
(Statman, unpublished); Brouwer and Veldman (1987). -/
public theorem_wanted graphContractability_npComplete :
    graphContractabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphContractabilityDec

end MetaMathlibExt.Complexity.NPComplete.GraphContractability
