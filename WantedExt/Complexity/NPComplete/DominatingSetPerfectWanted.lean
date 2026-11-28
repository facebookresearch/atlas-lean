/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for perfect graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
A. A. Bertossi, "Dominating sets for split and bipartite graphs", Information Processing
Letters 19(1) (1984), 37-40, doi:10.1016/0020-0190(84)90126-1;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetPerfectDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPerfect

open DominatingSet (DominatingSetInstance Graph DominatingSetFeasible)
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted (IsPerfect)

/-!
# DOMINATING SET for perfect graphs is NP-complete

INSTANCE: a perfect graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex `u ∈ V - V'` is joined to at least one member of `V'` by an
edge?

This is DOMINATING SET ([GT2], `DominatingSetDefs`) restricted to perfect graphs. Johnson's 1985
table and its 2022 revision by de Figueiredo, de Melo, Sasaki and Silva list the entry as
NP-complete. Bertossi proves DOMINATING SET NP-complete for bipartite graphs
(`DominatingSetBipartiteWanted`). Bipartite graphs are perfect (an induced subgraph with an edge has
chromatic number and clique number 2, one without edges has both equal to 1, or 0 when empty), so
Bertossi's reduction produces instances of this class. Membership in NP: a dominating set is a
certificate (every isolated vertex belongs to it, so it can be given on the non-isolated vertices
plus a count), and whether a graph is perfect is decidable in polynomial time: perfect graphs are
the Berge graphs (no odd hole or odd antihole) by the strong perfect graph theorem of Chudnovsky,
Robertson, Seymour and Thomas (Annals of Mathematics 164 (2006), 51-229,
doi:10.4007/annals.2006.164.51), and Berge graphs are recognized in polynomial time by Chudnovsky,
Cornuéjols, Liu, Seymour and Vušković ("Recognizing Berge graphs", Combinatorica 25 (2005), 143-186,
doi:10.1007/s00493-005-0012-8). Adding or removing isolated vertices does not change whether a graph
is perfect, so the binary vertex count does not make the problem succinct.

The instance, the graph, the parent well-formedness (a simple edge list) and the question are
those of DOMINATING SET (`DominatingSet.DominatingSetInstance`, `DominatingSet.Graph`,
`DominatingSet.WellFormed`, `DominatingSet.DominatingSetFeasible`: a `Finset` of at most `K`
vertices such that every vertex is in it or adjacent to one of its members); the restriction adds
to `WellFormed` that the graph is perfect and the bound `0 < K ≤ |V|` of [GT2].

A graph is perfect when every induced subgraph has chromatic number equal to its clique number;
this is MathlibExt's `MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect` (every
induced subgraph `G.induce s`, `s : Set V`, has `chromaticNumber = cliqueNum`), as in
`FeedbackVertexSetPerfectWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET for perfect graphs is NP-complete.** Source: Garey and Johnson (1979), [GT2];
Bertossi (1984); de Figueiredo, de Melo, Sasaki and Silva (2022), Table 1. -/
public theorem_wanted dominatingSetPerfect_npComplete :
    dominatingSetPerfectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetPerfectDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPerfect
