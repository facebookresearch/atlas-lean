/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on planar cubic graphs: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 3, DOMINATING SET [GT2]: the class for which
NP-completeness was proved is "3-regular planar graphs" (Garey and Johnson, unpublished result
(1978) cited in [G&J]; proved independently by T. Kikuno and Y. Kakuda, "The NP-completeness of
the dominating set problem in cubic planar graphs", manuscript (1979)), correcting the
"planar graphs that are regular of degree 4" of the [GT2] comment;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetPlanarMaxDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarCubic

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

open Classical in
/-- Well-formedness of an instance: a well-formed instance of DOMINATING SET on planar graphs of
maximum degree `3` (so `0 < K ≤ |V|` and the graph is planar) whose graph is regular of
degree `3`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSetPlanarMaxDegreeThree.WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- DOMINATING SET on planar cubic graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetPlanarCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarCubic
