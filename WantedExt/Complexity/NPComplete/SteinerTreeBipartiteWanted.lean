/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights on bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment
(attributed there to Berlekamp, 1976);
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartite

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS with unit weights on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)`, a subset `R ⊆ V` of terminals, and a positive integer
`K`.
QUESTION: is there a subtree of `G` that includes all the vertices of `R` and has at most `K`
edges?

This is STEINER TREE IN GRAPHS (Garey and Johnson [ND12], `SteinerTreeWanted`) with all edge
weights equal, restricted to bipartite graphs. The comment to [ND12] reads: "Remains
NP-complete if all edge weights are equal, even if G is a bipartite graph having no edges joining
two vertices in R or two vertices in V−R [Berlekamp, 1976]", a private communication that was
not available. Müller and Brandstädt prove NP-completeness for the subclass of chordal bipartite
graphs (title result; `SteinerTreeChordalBipartiteWanted`), which implies the bipartite case.
de Figueiredo, de Melo, Sasaki and Silva (Table 1, row BIPARTITE, column ST TREE) list the
problem as NP-complete, citing Garey and Johnson.

The instance type and the question are those of `WantedExt.Complexity.NPComplete.SteinerTreeWanted`
(`SteinerTree.SteinerTreeInstance`: a vertex count, weighted edges `(u, v, w)`, the terminals `R`
and the bound `K`; `SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at
most `K` connects all terminals). The restriction is added to `WellFormed`: the parent's
well-formedness, every edge weight equal to `1`, the graph of all edges
(`SteinerTree.Graph i i.2.1`) is bipartite (Mathlib's `SimpleGraph.IsBipartite`, that is,
`Colorable 2`), at least one vertex (a tree is nonempty, so the empty graph has no subtree), and
`0 < K` (Garey and Johnson's positive integer bound). With unit weights the total weight of an
edge set is its number of edges, and a connecting edge set contains a tree on the terminals with
no more edges (a single vertex when `R` is empty), so the question asks for a subtree of `G`
containing `R` with at most `K` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, its graph is bipartite, it has at least one vertex, and `K` is positive. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).IsBipartite ∧ 0 < i.1 ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS with unit weights on bipartite graphs is NP-complete.** Source:
Garey and Johnson (1979), [ND12]; Müller and Brandstädt (1987). -/
public theorem_wanted steinerTreeBipartite_npComplete :
    steinerTreeBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeBipartite
