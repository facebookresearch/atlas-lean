/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for perfect graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreePerfect

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted (IsPerfect)

/-!
# STEINER TREE IN GRAPHS (unit weights) for perfect graphs is NP-complete

INSTANCE: a perfect graph `G = (V, E)`, a set `R ⊆ V` of terminals and a positive integer `K`.
QUESTION: is there a subtree of `G` containing every vertex of `R` and having at most `K` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with unit edge weights, restricted to
perfect graphs. Johnson's 1985 table and its 2022 revision by de Figueiredo, de Melo, Sasaki and
Silva list the entry as NP-complete, citing Garey and Johnson. Müller and Brandstädt prove the
unweighted problem NP-complete for chordal bipartite graphs (`SteinerTreeChordalBipartiteWanted`,
with the number of vertices of the tree as the bound; a tree with at most `K + 1` vertices has at
most `K` edges, so the two bounds are interchangeable). Bipartite graphs are perfect (an induced
subgraph with an edge has chromatic number and clique number 2, one without edges has both equal to
1, or 0 when empty), so that reduction produces instances of this class. Membership in NP: a set of
edges connecting the terminals is a certificate, and whether a graph is perfect is decidable in
polynomial time: perfect graphs are the Berge graphs (no odd hole or odd antihole) by the strong
perfect graph theorem of Chudnovsky, Robertson, Seymour and Thomas (Annals of Mathematics 164
(2006), 51-229, doi:10.4007/annals.2006.164.51), and Berge graphs are recognized in polynomial time
by Chudnovsky, Cornuéjols, Liu, Seymour and Vušković ("Recognizing Berge graphs", Combinatorica 25
(2005), 143-186, doi:10.1007/s00493-005-0012-8). Adding or removing isolated vertices does not
change whether a graph is perfect, so the binary vertex count does not make the problem succinct (an
isolated terminal makes the instance a no-instance unless it is the only terminal).

The instance (vertex count, weighted edge list, terminals, budget), the parent's
well-formedness and the question (a sub-list of the edges of total weight at most `K` connecting
all terminals; a minimal such edge set is a tree) are those of `SteinerTreeWanted`, as in
`SteinerTreeSplitGraphsWanted`; the restriction adds to `WellFormed` that every edge has weight
`1`, that the graph `SteinerTree.Graph i i.2.1` is perfect, and `0 < K` (Garey and Johnson's
"positive integer").

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

/-- Well-formedness of an instance: a well-formed STEINER TREE IN GRAPHS instance in which every
edge has weight `1`, whose graph is perfect, and `0 < K`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    IsPerfect (SteinerTree.Graph i i.2.1) ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for perfect graphs as a decision problem over bitstrings.
-/
noncomputable def steinerTreePerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS (unit weights) for perfect graphs is NP-complete.** Source: Garey and
Johnson (1979), [ND12]; Müller and Brandstädt (1987); de Figueiredo, de Melo, Sasaki and Silva
(2022), Table 1. -/
public theorem_wanted steinerTreePerfect_npComplete :
    steinerTreePerfectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreePerfectDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreePerfect
