/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) on comparability graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment
("Remains NP-complete if all edge weights are equal, even if G is a bipartite graph having no
edges joining two vertices in R or two vertices in V-R [Berlekamp, 1976]");
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (comparability graphs, unweighted
STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson);
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53(2-3) (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SteinerTreeComparabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeComparability

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) on comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)` with weight `w(e) = 1` for each `e ∈ E`, a subset
`R ⊆ V`, and a positive integer bound `B`.
QUESTION: is there a subtree of `G` that includes all the vertices of `R` and such that the sum
of the weights of the edges in the subtree (its number of edges) is no more than `B`?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with all edge weights equal (the
unweighted problem of Johnson's Table 1), restricted to comparability graphs. Garey and Johnson
record that the equal-weight problem remains NP-complete for bipartite graphs (attributed to
Berlekamp, 1976; the original was not available), Johnson's Table 1 (1985) lists it as
NP-complete for comparability graphs citing Garey and Johnson, and Müller and Brandstädt (1987)
prove it NP-complete for chordal bipartite graphs. Every bipartite graph is a comparability
graph: ordering each vertex of one side below its neighbors on the other side is a strict partial
order (there are no chains of length 2, so transitivity holds vacuously) whose comparable pairs
are exactly the edges. Membership in NP: the certificate is the tree together with a transitive
orientation of `G`, both checkable in polynomial time.

The instance type and the question are those of
`WantedExt.Complexity.NPComplete.SteinerTreeWanted` (`SteinerTree.SteinerTreeInstance`: a vertex
count, weighted edges `(u, v, w)`, the terminals `R` and the bound `B`;
`SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at most `B` connects
all terminals, and a connecting edge set contains a tree of no greater weight). The restriction
is added to `WellFormed`: the parent's well-formedness, every edge weight equal to `1`, the graph
of all edges (`SteinerTree.Graph i i.2.1`) is a comparability graph
(`ComparabilityGraphSandwich.IsComparabilityGraph` from
`WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted`: some strict partial order `r`
on the vertices, Mathlib's `IsStrictOrder`, makes two vertices adjacent exactly when they are
comparable under `r`), at least one vertex (so that a subtree exists when `R` is empty), and
`0 < B` as in [ND12].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STEINER TREE IN GRAPHS (unit weights) on comparability graphs is NP-complete.** Source:
Garey and Johnson (1979), [ND12], comment; Johnson (1985), Table 1; Müller and Brandstädt
(1987). -/
public theorem_wanted steinerTreeComparability_npComplete :
    steinerTreeComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeComparability
