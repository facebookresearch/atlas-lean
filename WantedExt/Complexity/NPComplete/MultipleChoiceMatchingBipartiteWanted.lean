/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE MATCHING (bipartite, classes of at most 2 edges, K = |V|/2) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT55] MULTIPLE CHOICE MATCHING,
p. 203 (comment: "Remains NP-complete even if `G` is bipartite, each `Eᵢ` contains at most 2
edges, and `K = |V|/2`."), crediting [Valiant, 1977c], [Itai and Rodeh, 1977a] and
[Itai, Rodeh, and Tanimoto, 1978];
A. Itai, M. Rodeh and S. L. Tanimoto, "Some matching problems for bipartite graphs",
Journal of the ACM 25 (1978), 517-525, doi:10.1145/322092.322093;
A. Itai and M. Rodeh, "Some matching problems", Automata, Languages and Programming (ICALP
1977), Lecture Notes in Computer Science 52, Springer (1977), 258-268,
doi:10.1007/3-540-08342-1_20.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import WantedExt.Complexity.NPComplete.MultipleChoiceMatchingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatchingBipartite

open MultipleChoiceMatching (MultipleChoiceMatchingInstance Graph
  MultipleChoiceMatchingFeasible)

/-!
# MULTIPLE CHOICE MATCHING (bipartite, classes of at most 2 edges, K = |V|/2) is NP-complete

Given a graph `G = (V, E)` that is bipartite, a partition of `E` into disjoint sets
`E₁, E₂, ..., E_J` each containing at most 2 edges, and the positive integer `K = |V|/2`, is
there a subset `E' ⊆ E` with `|E'| ≥ K` such that no two edges in `E'` share a common vertex
and such that `E'` contains at most one edge from each `Eᵢ`?

This is the restriction of MULTIPLE CHOICE MATCHING ([GT55], `MultipleChoiceMatchingWanted`)
named in the entry's comment, with its three conditions together. The instance type, the graph
and `MultipleChoiceMatching.MultipleChoiceMatchingFeasible` are the parent's, unchanged: each
edge is listed once as a triple `(u, v, c)` saying that the edge `{u, v}` lies in the class
`E_c`, and `E'` is the edge set of a matching subgraph. `WellFormed` adds the restrictions:
* bipartite: Mathlib's `SimpleGraph.IsBipartite` (2-colorability);
* each class has at most 2 edges: at most 2 listed edges carry the label `c`, for every `c`
  (each edge is listed once, so this counts the edges of `E_c`);
* `K = |V|/2`: `2 * K = n`, so a feasible `E'` is a perfect matching.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list in range, each edge
listed once with one class label, `K` positive), the graph is bipartite, every class contains
at most 2 edges, and `K = |V|/2`. -/
def WellFormed (i : MultipleChoiceMatchingInstance) : Prop :=
  MultipleChoiceMatching.WellFormed i ∧ (Graph i).IsBipartite ∧
    (∀ c, (i.2.1.filter fun e => e.2.2 = c).length ≤ 2) ∧ 2 * i.2.2 = i.1

open Classical in
/-- MULTIPLE CHOICE MATCHING restricted to bipartite graphs, classes of at most 2 edges and
`K = |V|/2`, as a decision problem over bitstrings. -/
noncomputable def multipleChoiceMatchingBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleChoiceMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceMatchingFeasible i)
  | none => false

/-- **MULTIPLE CHOICE MATCHING is NP-complete for bipartite graphs, classes of at most 2
edges and `K = |V|/2`.** Source: Garey and Johnson (1979), [GT55], comment; Itai, Rodeh and
Tanimoto (1978); Itai and Rodeh (1977). -/
public theorem_wanted multipleChoiceMatchingBipartite_npComplete :
    multipleChoiceMatchingBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceMatchingBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceMatchingBipartite
