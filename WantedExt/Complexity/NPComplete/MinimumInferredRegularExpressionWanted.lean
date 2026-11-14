/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED REGULAR EXPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL10] MINIMUM INFERRED
REGULAR EXPRESSION;
D. Angluin, "On the complexity of minimum inference of regular sets", Information and
Control 39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Languages.KleeneConverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression

/-!
# MINIMUM INFERRED REGULAR EXPRESSION is NP-complete

Given a finite alphabet `Σ`, two finite sets `S, T ⊆ Σ*` and a positive integer `K`, is there
a regular expression `E` over `Σ` with `K` or fewer occurrences of symbols from `Σ` such that,
if `L` is the language of `E`, then `S ⊆ L` and `T ⊆ Σ* - L`?

The alphabet is `Σ = {0, ..., k - 1}`, words are lists of naturals, and the finite sets `S`
and `T` are lists of words (a repeated word does not change the question). Regular
expressions are Mathlib's `RegularExpression` (atoms `0` for the empty language, `1` for the
empty word, and letters; operators `+`, `*` and Kleene star), with language
`RegularExpression.matches'`. The size of `E` is the number of letter occurrences,
`symbolOccurrences E`; the atoms `0` and `1` and the operators are not counted.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMUM INFERRED REGULAR EXPRESSION is NP-complete.** Source: Garey and Johnson (1979),
[AL10]; Angluin (1978). -/
public theorem_wanted minimumInferredRegularExpression_npComplete :
    minimumInferredRegularExpressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumInferredRegularExpressionDec

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredRegularExpression
