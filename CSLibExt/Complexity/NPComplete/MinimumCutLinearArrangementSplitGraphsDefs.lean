/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for split graphs: definitions

Source:
P. Heggernes, D. Lokshtanov, R. Mihai and C. Papadopoulos, "Cutwidth of split graphs, threshold
graphs, and proper interval graphs", in *Graph-Theoretic Concepts in Computer Science (WG 2008)*,
Lecture Notes in Computer Science 5344, Springer (2008), 218-229,
doi:10.1007/978-3-540-92248-3_20;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetSplitGraphsDefs
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)

/-- Well-formedness of an instance: the parent's (the edge list describes a simple graph on
`0, ..., n - 1`, and `0 < K`), and the graph is a split graph. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  MinimumCutLinearArrangement.WellFormed i ∧
    DominatingSetSplitGraphs.IsSplitGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1)

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for split graphs as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementSplitGraphs
