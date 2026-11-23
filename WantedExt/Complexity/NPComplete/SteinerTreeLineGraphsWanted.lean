/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for line graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS; D. S. Johnson, "The
NP-completeness column: an ongoing guide" (sixteenth edition), Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or Line)", column "StTree" for
(unweighted) STEINER TREE IN GRAPHS: "N [70]", reference [70] being a private communication of A.
Schaffer); H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van
Leeuwen, "Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical
Computer Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (Lemma 8 and Observation 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeLineGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) for line graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is an edge (line) graph, a subset `R ⊆ V`, and a positive
integer `K`. QUESTION: is there a subtree of `G` that includes all the vertices of `R` and has at
most `K` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with all edge weights equal to 1,
restricted to line graphs. Bodlaender et al. prove the unweighted vertex version NP-complete for
line graphs (Lemma 8) and observe that the unweighted edge and vertex versions are equivalent, a
tree on `m` vertices having `m - 1` edges (Observation 1). The instance type,
`SteinerTree.WellFormed` and `SteinerTree.SteinerTreeFeasible` (an edge sublist of total weight at
most `K` in which the vertices of `R` are pairwise reachable) are the parent's, unchanged.
`WellFormed` adds unit weights (as in `SteinerTreeSplitGraphsWanted`), the restriction
`MetaMathlibExt.SimpleGraph.IsLineGraph` (from `MathlibExt.Combinatorics.SimpleGraph.LineGraph`:
isomorphic to Mathlib's `SimpleGraph.lineGraph` of a graph on some `Fin k`), as in
`LineGraphHamiltonianCircuitWanted`, the source's `0 < K`, and `0 < n` (with no vertices the
parent's feasibility condition would hold vacuously, although the empty graph has no subtree).
The instance is the line graph itself. Bodlaender et al. state their problems for connected
graphs; Garey and Johnson's problem,
stated here, has no connectivity condition (a disconnected instance is a no-instance unless `R`
lies in one component).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (simple weighted edge list, terminals listed
once and below `n`), every edge weight is 1, the graph is a line graph, `K` is positive, and the
graph has a vertex. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    MetaMathlibExt.SimpleGraph.IsLineGraph (SteinerTree.Graph i i.2.1) ∧ 0 < i.2.2.2 ∧
      0 < i.1

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for line graphs as a decision problem over bitstrings. -/
noncomputable def steinerTreeLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS with unit weights is NP-complete for line graphs.** Source: Garey
and Johnson (1979), [ND12]; Johnson, NP-completeness column (1985), Table 1; Bodlaender et al.
(2021). -/
public theorem_wanted steinerTreeLineGraphs_npComplete :
    steinerTreeLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeLineGraphs
