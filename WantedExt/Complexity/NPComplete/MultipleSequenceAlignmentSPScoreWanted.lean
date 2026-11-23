/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is NP-complete

Source:
I. Elias, "Settling the intractability of multiple alignment", Journal of Computational
Biology 13 (2006), 1323-1339, doi:10.1089/cmb.2006.13.1323 (NP-hard for every metric over a
binary or larger alphabet, in particular the unit metric);
earlier: L. Wang and T. Jiang, "On the complexity of multiple sequence alignment", Journal of
Computational Biology 1 (1994), 337-348, doi:10.1089/cmb.1994.1.337 (a non-metric score).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleSequenceAlignment
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore

/-!
# MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is NP-complete

INSTANCE: strings `s₁, …, s_k` over the binary alphabet `{0, 1}` (`k` is part of the input) and
a non-negative integer `K`. QUESTION: is there a multiple alignment of `s₁, …, s_k` whose
sum-of-pairs (SP) score under the unit metric is at most `K`? A multiple alignment pads every
`sᵢ` with gaps `-` to a common length, with no column consisting of gaps only; its SP-score is
the sum over all pairs `i < j` of rows and over all columns of `d(x, y)`, where `x` and `y` are
the symbols of rows `i` and `j` in the column and the unit metric `d` on `{0, 1, -}` is `0` on
equal symbols and `1` on distinct ones.

The alignment and its SP-score are CSLib's: an alignment is
`Cslib.Algorithms.Lean.MSAlignment k Bool`, a list of columns, each assigning every row a letter
(`some b`) or a gap (`none`); `Cslib.Algorithms.Lean.IsMSAlignment` says no column is all gaps
and row `i` with its gaps removed is `sᵢ`; `Cslib.Algorithms.Lean.msaScore σ gap` is the SP-score
with substitution score `σ`, score `gap` for a letter against a gap and `0` for two gaps. The unit
metric is `σ a b = if a = b then 0 else 1` with `gap = 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is
NP-complete.** Source: Elias (2006). -/
public theorem_wanted multipleSequenceAlignmentSPScore_npComplete :
    multipleSequenceAlignmentSPScoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleSequenceAlignmentSPScoreDec

end MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore
