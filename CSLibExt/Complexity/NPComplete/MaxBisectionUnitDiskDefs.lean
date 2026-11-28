/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM BISECTION on unit disk graphs: definitions

Source:
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint
arXiv:cs/0609128), Corollary 11;
ISGCI, class "unit disk" (gc_389), problem Maximum bisection, NP-complete.
-/
module

public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxBisectionPlanarDefs
public import CSLibExt.Complexity.NPComplete.MaxCutUnitDiskGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxBisectionUnitDisk

open MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
  (MaxCutUnitDiskGraphsInstance toMaxCut)

/-- A bisection of the graph with at least `K` edges between its two sides. -/
def MaxBisectionUnitDiskFeasible (i : MaxCutUnitDiskGraphsInstance) : Prop :=
  MaxBisectionPlanar.MaxBisectionFeasible (toMaxCut i)

open Classical in
/-- MAXIMUM BISECTION on unit disk graphs as a decision problem over bitstrings. -/
noncomputable def maxBisectionUnitDiskDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutUnitDiskGraphsInstance) x with
  | some i => decide (MaxCutUnitDiskGraphs.WellFormed i ∧ MaxBisectionUnitDiskFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxBisectionUnitDisk
