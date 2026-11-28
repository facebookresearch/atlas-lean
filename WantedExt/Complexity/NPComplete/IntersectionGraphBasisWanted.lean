/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH BASIS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT59] INTERSECTION GRAPH BASIS;
L. T. Kou, L. J. Stockmeyer and C. K. Wong, "Covering edges by cliques with regard to keyword
conflicts and intersection graphs", Communications of the ACM 21 (1978), 135-139,
doi:10.1145/359340.359346;
J. Orlin, "Contentment in graph theory: covering graphs with cliques", Indagationes
Mathematicae (Proceedings) 80 (1977), 406-424, doi:10.1016/1385-7258(77)90055-5;
P. Erdős, A. W. Goodman and L. Pósa, "The representation of a graph by set intersections",
Canadian Journal of Mathematics 18 (1966), 106-112, doi:10.4153/CJM-1966-014-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntersectionGraphBasisDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphBasis

/-!
# INTERSECTION GRAPH BASIS is NP-complete

Given a graph `G = (V, E)` and a positive integer `K ≤ |E|`, is there a finite set `S` with
`|S| ≤ K` and a subset `S[v] ⊆ S` for each `v ∈ V` such that `{u, v} ∈ E` if and only if
`S[u]` and `S[v]` intersect?

The ground set is `S = Fin k` with `k ≤ K`, and `S[v]` is a `Finset (Fin k)`; the condition
is required for distinct `u, v` (a simple graph has no loops). Erdős, Goodman and Pósa (1966)
showed that the least such `|S|` (the intersection number) equals the least number of cliques
covering the edges, so this problem is polynomially equivalent to COVERING BY CLIQUES
(`CoveringByCliquesWanted`), from which Garey and Johnson transform it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTERSECTION GRAPH BASIS is NP-complete.** Source: Garey and Johnson (1979), [GT59];
Kou, Stockmeyer and Wong (1978); Orlin (1977). -/
public theorem_wanted intersectionGraphBasis_npComplete :
    intersectionGraphBasisDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intersectionGraphBasisDec

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphBasis
