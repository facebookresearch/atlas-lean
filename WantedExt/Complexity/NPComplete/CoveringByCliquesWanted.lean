/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING BY CLIQUES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT17] COVERING BY
CLIQUES;
L. T. Kou, L. J. Stockmeyer, and C. K. Wong, "Covering edges by cliques with
regard to keyword conflicts and intersection graphs", Communications of the ACM
21 (1978), 135-139, doi:10.1145/359340.359346;
J. Orlin, "Contentment in graph theory: covering graphs with cliques",
Indagationes Mathematicae (Proceedings) 80 (1977), 406-424,
doi:10.1016/1385-7258(77)90055-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CoveringByCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringByCliques

/-!
# COVERING BY CLIQUES is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: are there `k ≤ K`
subsets `V₁, ..., Vₖ` of `V` such that each `Vᵢ` induces a complete subgraph of `G` and such
that for each edge `{u, v} ∈ E` there is some `Vᵢ` that contains both `u` and `v`?

"Induces a complete subgraph" is Mathlib's `IsClique`. Under `WellFormed` the edge list has
one entry per edge, so its length is `|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COVERING BY CLIQUES is NP-complete.** Source: Garey and Johnson (1979), [GT17];
Kou, Stockmeyer, and Wong (1978); Orlin (1977). -/
public theorem_wanted coveringByCliques_npComplete :
    coveringByCliquesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coveringByCliquesDec

end MetaMathlibExt.Complexity.NPComplete.CoveringByCliques
