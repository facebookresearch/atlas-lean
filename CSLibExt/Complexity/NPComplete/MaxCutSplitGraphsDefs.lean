/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on split graphs: definitions

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal of
Computing 7(1) (2000), 14-31 (conference version: STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetSplitGraphsDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs (IsSplitGraph)

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev MaxCutSplitGraphsInstance := MaxCutInstance

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a split graph, and `0 < K`. -/
def WellFormed (i : MaxCutSplitGraphsInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsSplitGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def MaxCutSplitGraphsFeasible (i : MaxCutSplitGraphsInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- MAX CUT on split graphs as a decision problem over bitstrings. -/
noncomputable def maxCutSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutSplitGraphsInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutSplitGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxCutSplitGraphs
