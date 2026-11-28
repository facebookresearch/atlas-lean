/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for grid graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of
Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Grid", column
"StTree" for (unweighted) STEINER TREE IN GRAPHS: "N [35]");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeGridGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- Well-formedness of an instance: the parent's (simple weighted edge list, terminals listed
once and below `n`), every edge weight is 1, the graph is a subgraph of the grid up to
isomorphism, `K` is positive, and the graph has a vertex. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).IsContained (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ) ∧
    0 < i.2.2.2 ∧ 0 < i.1

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on grid graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeGridGraphs
