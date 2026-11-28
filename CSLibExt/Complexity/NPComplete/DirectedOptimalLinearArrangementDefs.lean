/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED OPTIMAL LINEAR ARRANGEMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT43] DIRECTED OPTIMAL LINEAR
ARRANGEMENT (reference: [Even and Shiloach, 1975], transformation from OPTIMAL LINEAR
ARRANGEMENT); S. Even and Y. Shiloach, "NP-completeness of several arrangement problems",
Technical Report 43, Department of Computer Science, Technion, Haifa (1975) (not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedOptimalLinearArrangement

/-- An instance: vertex count `n`, arc list, bound `K`. -/
abbrev DirectedOptimalLinearArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the arcs are distinct, join vertices below `n`, and are not
loops; `0 < K`. -/
def WellFormed (i : DirectedOptimalLinearArrangementInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧ 0 < i.2.2

/-- An ordering of the vertices in which every arc goes forward and the arc lengths sum to at
most `K`. -/
def DirectedOptimalLinearArrangementFeasible (i : DirectedOptimalLinearArrangementInstance) :
    Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    (∀ a ∈ i.2.1, perm.idxOf a.1 < perm.idxOf a.2) ∧
    (i.2.1.map fun a => perm.idxOf a.2 - perm.idxOf a.1).sum ≤ i.2.2

open Classical in
/-- DIRECTED OPTIMAL LINEAR ARRANGEMENT as a decision problem over bitstrings. -/
noncomputable def directedOptimalLinearArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedOptimalLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ DirectedOptimalLinearArrangementFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedOptimalLinearArrangement
