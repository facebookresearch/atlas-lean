/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet): definitions

Source:
I. Elias, "Settling the intractability of multiple alignment", Journal of Computational
Biology 13 (2006), 1323-1339, doi:10.1089/cmb.2006.13.1323 (NP-hard for every metric over a
binary or larger alphabet, in particular the unit metric);
earlier: L. Wang and T. Jiang, "On the complexity of multiple sequence alignment", Journal of
Computational Biology 1 (1994), 337-348, doi:10.1089/cmb.1994.1.337 (a non-metric score).
-/
module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleSequenceAlignment
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore

/-- An instance: the binary strings `s₁, …, s_k` and the bound `K`. -/
abbrev MultipleSequenceAlignmentSPScoreInstance := List (List Bool) × ℕ

/-- Every instance is well formed: any list of binary strings and any bound. -/
def WellFormed (_i : MultipleSequenceAlignmentSPScoreInstance) : Prop := True

/-- The unit metric on letters: `0` for equal letters and `1` for distinct ones (a letter
against a gap scores `1` through the `gap` argument of `msaScore`). -/
def unitScore (a b : Bool) : ℤ := if a = b then 0 else 1

/-- Some multiple alignment of the strings has SP-score at most `K` under the unit metric. -/
def MultipleSequenceAlignmentSPScoreFeasible
    (i : MultipleSequenceAlignmentSPScoreInstance) : Prop :=
  ∃ A : Cslib.Algorithms.Lean.MSAlignment i.1.length Bool,
    Cslib.Algorithms.Lean.IsMSAlignment (fun j => i.1.get j) A ∧
      Cslib.Algorithms.Lean.msaScore unitScore 1 A ≤ (i.2 : ℤ)

open Classical in
/-- MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) as a decision
problem over bitstrings. -/
noncomputable def multipleSequenceAlignmentSPScoreDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleSequenceAlignmentSPScoreInstance) x with
  | some i => decide (WellFormed i ∧ MultipleSequenceAlignmentSPScoreFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore
