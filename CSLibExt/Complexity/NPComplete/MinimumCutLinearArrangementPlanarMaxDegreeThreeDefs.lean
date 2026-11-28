/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar graphs of maximum degree 3: definitions

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58(1-3) (1988), 209-229, doi:10.1016/0304-3975(88)90028-X (abstract: "derive
from this the NP-completeness of Min Cut for planar graphs with maximum vertex degree 3");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)

open Classical in
/-- Well-formedness of an instance: the parent's (the edge list describes a simple graph on
`0, ..., n - 1`, and `0 < K`), and the graph is planar with every vertex degree at most `3`. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  MinimumCutLinearArrangement.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar ∧
      ∀ v, (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).degree v ≤ 3

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for planar graphs of maximum degree 3 as a decision problem
over bitstrings. -/
noncomputable def minimumCutLinearArrangementPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementPlanarMaxDegreeThree
