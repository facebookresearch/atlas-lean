/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR GRAPH 3-COLORABILITY (maximum degree 4) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
NP-complete for `K = 3` and planar graphs with no vertex degree exceeding 4);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
L. Stockmeyer, "Planar 3-colorability is polynomial complete", ACM SIGACT News 5(3) (1973),
19-25, doi:10.1145/1008293.1008294.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarDegreeFourThreeColorabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarDegreeFourThreeColorability

/-!
# PLANAR GRAPH 3-COLORABILITY (maximum degree 4) is NP-complete

An instance is a planar graph `G = (V, E)` in which no vertex has degree exceeding 4. The
question is whether `G` is 3-colorable. This is the restriction of GRAPH K-COLORABILITY to
`K = 3` and planar graphs of maximum degree at most 4 (Garey, Johnson and Stockmeyer 1976;
Stockmeyer 1973 for planar graphs).

The graph is simple and given by an edge list on `Fin n`. Planarity is the shared MathlibExt
predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem this
is planarity for finite simple graphs). The degree of `v` is the cardinality of its neighbour
set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR GRAPH 3-COLORABILITY (maximum degree 4) is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Garey, Johnson and Stockmeyer (1976). -/
public theorem_wanted planarDegreeFourThreeColorability_npComplete :
    planarDegreeFourThreeColorabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarDegreeFourThreeColorabilityDec

end MetaMathlibExt.Complexity.NPComplete.PlanarDegreeFourThreeColorability
