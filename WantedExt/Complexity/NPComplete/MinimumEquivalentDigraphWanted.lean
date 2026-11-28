/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM EQUIVALENT
DIGRAPH; A. V. Aho, M. R. Garey, and J. D. Ullman, "The transitive reduction of a directed
graph", SIAM Journal on Computing 1 (1972), 131-137 (distinguishing transitive reduction from
the minimum equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson,
"An algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumEquivalentDigraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph

/-!
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

A directed graph and a bound `K`. The question is whether some spanning subdigraph with at most
`K` arcs has exactly the same reachability relation: two vertices are joined by a directed path
in the subdigraph iff they are in the original. Reachability is witnessed by paths of length at
most `n + 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM EQUIVALENT DIGRAPH is NP-complete.** The decision problem MINIMUM EQUIVALENT
DIGRAPH belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction
to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM EQUIVALENT DIGRAPH; A. V. Aho, M. R. Garey,
and J. D. Ullman, "The transitive reduction of a directed graph", SIAM Journal on
Computing 1 (1972), 131-137 (distinguishing transitive reduction from the minimum
equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson, "An
algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460. -/
public theorem_wanted minimumEquivalentDigraph_npComplete :
    minimumEquivalentDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEquivalentDigraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph
