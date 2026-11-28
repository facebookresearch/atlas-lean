/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on interval graphs: definitions

Source:
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70(2) (2023), 307-322, doi:10.1007/s00454-022-00472-y
(SoCG 2021; preprint arXiv:2006.00061).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntervalGraphCompletionDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutIntervalGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-- An instance: the vertex count `n`, the edge list, and the bound `k`; this is the MAXIMUM
CUT instance type. -/
abbrev MaxCutIntervalGraphsInstance := MaxCutInstance

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is an interval graph, and `1 ≤ k ≤ |E|`. -/
def WellFormed (i : MaxCutIntervalGraphsInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsIntervalGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    1 ≤ i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A partition `A = S`, `B = V - S` with at least `k` edges between the two sets (the MAXIMUM
CUT question). -/
def MaxCutIntervalGraphsFeasible (i : MaxCutIntervalGraphsInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- MAX CUT on interval graphs as a decision problem over bitstrings. -/
noncomputable def maxCutIntervalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutIntervalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutIntervalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxCutIntervalGraphs
