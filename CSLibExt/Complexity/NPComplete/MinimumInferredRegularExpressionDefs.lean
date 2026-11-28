/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED REGULAR EXPRESSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL10] MINIMUM INFERRED
REGULAR EXPRESSION;
D. Angluin, "On the complexity of minimum inference of regular sets", Information and
Control 39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6.
-/
module

public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression

/-- An instance: the alphabet size `k` (the alphabet is `{0, ..., k - 1}`), the words `S`
the expression must match, the words `T` it must not match, and the bound `K`. -/
abbrev MinimumInferredRegularExpressionInstance := ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- The number of occurrences of alphabet symbols in a regular expression: each letter
`char a` counts once per occurrence; `0`, `1` and the operators count nothing. -/
def symbolOccurrences {α : Type*} : RegularExpression α → ℕ
  | .zero => 0
  | .epsilon => 0
  | .char _ => 1
  | .plus P Q => symbolOccurrences P + symbolOccurrences Q
  | .comp P Q => symbolOccurrences P + symbolOccurrences Q
  | .star P => symbolOccurrences P

/-- Well-formedness of an instance: every word of `S` and of `T` is over the alphabet
`{0, ..., k - 1}`, and `K` is positive. -/
def WellFormed (i : MinimumInferredRegularExpressionInstance) : Prop :=
  (∀ s ∈ i.2.1, ∀ a ∈ s, a < i.1) ∧ (∀ t ∈ i.2.2.1, ∀ a ∈ t, a < i.1) ∧ 0 < i.2.2.2

/-- Some regular expression over the alphabet `{0, ..., k - 1}` with at most `K` symbol
occurrences matches every word of `S` and no word of `T`. -/
def MinimumInferredRegularExpressionFeasible
    (i : MinimumInferredRegularExpressionInstance) : Prop :=
  ∃ E : RegularExpression ℕ,
    (∀ a ∈ Cslib.Language.KleeneConverse.regexLetters E, a < i.1) ∧
      symbolOccurrences E ≤ i.2.2.2 ∧
      (∀ s ∈ i.2.1, s ∈ E.matches') ∧
      ∀ t ∈ i.2.2.1, t ∉ E.matches'

open Classical in
/-- MINIMUM INFERRED REGULAR EXPRESSION as a decision problem over bitstrings. -/
noncomputable def minimumInferredRegularExpressionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredRegularExpressionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumInferredRegularExpressionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
