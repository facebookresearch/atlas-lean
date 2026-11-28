/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for line graphs: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeLineGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeLineGraphs
