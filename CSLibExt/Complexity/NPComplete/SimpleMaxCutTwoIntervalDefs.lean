/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on 2-interval graphs: definitions

Source:
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1
(MAX CUT is NP-complete on interval graphs);
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal
of Computing 7 (2000), 14-31 (the reference ISGCI gives for this class);
ISGCI, class "2-interval" (gc_40), problem Maximum cut, NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntervalNumberAtMostKDefs
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoInterval

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK (IsMultipleIntervalGraph)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a 2-interval graph, and `1 ≤ K ≤ |E|`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsMultipleIntervalGraph 2 (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    1 ≤ i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A partition `A = S`, `B = V - S` with at least `K` edges between the two sets (the MAXIMUM
CUT question). -/
def SimpleMaxCutTwoIntervalFeasible (i : MaxCutInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on 2-interval graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutTwoIntervalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutTwoIntervalFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoInterval
