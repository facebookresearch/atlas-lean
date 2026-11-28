/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSHUFFLING A SQUARE: definitions

Source:
S. Buss and M. Soltys, "Unshuffling a square is NP-hard", Journal of Computer and System
Sciences 80(4) (2014), 766-776, doi:10.1016/j.jcss.2013.11.002, arXiv:1211.7161
(Section 1, definition of shuffle and square; Theorem 3).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Languages.Shuffle

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShuffleSquare

/-- An instance: the string `w`, a list of symbols. -/
abbrev ShuffleSquareInstance := List ℕ

/-- Well-formedness of an instance: every string of symbols is an instance. -/
def WellFormed (_i : ShuffleSquareInstance) : Prop := True

/-- `w` is a square: `w = u ⊙ u` for some string `u`. -/
def ShuffleSquareFeasible (i : ShuffleSquareInstance) : Prop :=
  ∃ u : List ℕ, Cslib.Language.IsShuffle u u i

open Classical in
/-- UNSHUFFLING A SQUARE as a decision problem over bitstrings. -/
noncomputable def shuffleSquareDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShuffleSquareInstance) x with
  | some i => decide (WellFormed i ∧ ShuffleSquareFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShuffleSquare
