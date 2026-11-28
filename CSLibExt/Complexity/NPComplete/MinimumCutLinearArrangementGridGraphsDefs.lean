/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT for grid graphs: definitions

Source:
J. Díaz, M. D. Penrose, J. Petit and M. Serna, "Linear orderings of random geometric graphs
(extended abstract)", in *Graph-Theoretic Concepts in Computer Science (WG '99)*, Lecture Notes
in Computer Science 1665 (1999), 291-302, doi:10.1007/3-540-46784-X_28, Theorem 1 ("Bandwidth,
MinCut and VertSep remain NP-complete even when restricted to grid graphs"); full version:
"Approximating layout problems on random geometric graphs", Journal of Algorithms 39(1) (2001),
78-116, doi:10.1006/jagm.2000.1149;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementGridGraphs

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance gridEdges)

/-- An instance: the points of the grid graph and the bound `K`. -/
abbrev MinimumCutLinearArrangementGridGraphsInstance := GridGraphHamiltonianCircuitInstance × ℕ

/-- The grid graph and the bound as a MINIMUM CUT LINEAR ARRANGEMENT instance: `|V|` vertices,
the grid edges, and `K`. -/
def toMinimumCutLinearArrangementInstance (i : MinimumCutLinearArrangementGridGraphsInstance) :
    MinimumCutLinearArrangement.MinimumCutLinearArrangementInstance :=
  (i.1.length, gridEdges i.1, i.2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (`V` is a set), and
`0 < K`. -/
def WellFormed (i : MinimumCutLinearArrangementGridGraphsInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i.1 ∧ 0 < i.2

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for grid graphs as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementGridGraphsInstance) x with
  | some i =>
    decide (WellFormed i ∧ MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible
      (toMinimumCutLinearArrangementInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementGridGraphs
