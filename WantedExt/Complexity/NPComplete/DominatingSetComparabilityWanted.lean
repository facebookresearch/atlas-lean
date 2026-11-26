/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on comparability graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, the problem
restricted here;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (comparability graphs, DOMINATING SET:
NP-complete);
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53(2-3) (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetComparability

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K`, that is, every vertex not in `V'`
has a neighbor in `V'`?

The instance, the graph and the question are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds that the graph is a comparability graph,
and `0 < K ≤ |V|` as in [GT2].

A comparability graph (a transitively orientable graph) is the comparability graph of a partial
order: `ComparabilityGraphSandwich.IsComparabilityGraph` from
`WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted` (some strict partial order `r`
on the vertices, Mathlib's `IsStrictOrder`, makes two vertices adjacent exactly when they are
comparable under `r`), as in `FeedbackVertexSetComparabilityWanted`.

Johnson's Table 1 (1985) lists DOMINATING SET as NP-complete for comparability graphs, and
de Figueiredo, de Melo, Sasaki and Silva (2022) cite Müller and Brandstädt (1987) for that entry.
Müller and Brandstädt prove DOMINATING SET NP-complete for chordal bipartite graphs. Every
bipartite graph is a comparability graph: ordering each vertex of one side below its neighbors on
the other side is a strict partial order (there are no chains of length 2, so transitivity holds
vacuously) whose comparable pairs are exactly the edges. Their reduction therefore outputs
instances of this problem. Membership in NP: the certificate is `V'` together with a transitive
orientation of `G`, both checkable in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance (a simple edge list on
`Fin n`) whose graph is a comparability graph, with `0 < K ≤ |V| = n`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ ComparabilityGraphSandwich.IsComparabilityGraph (Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET on comparability graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on comparability graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT2]; Johnson (1985), Table 1; Müller and Brandstädt (1987). -/
public theorem_wanted dominatingSetComparability_npComplete :
    dominatingSetComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetComparability
