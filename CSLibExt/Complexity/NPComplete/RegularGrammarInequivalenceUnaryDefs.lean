/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR GRAMMAR INEQUIVALENCE over a one-letter alphabet: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL14] REGULAR GRAMMAR INEQUIVALENCE,
p. 269, comment: the general problem is NP-complete if `|Σ| = 1` (no separate
citation; the related [AL9] comment records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete if `|Σ| = 1`, citing L. J. Stockmeyer and A. R. Meyer, "Word problems requiring
exponential time (preliminary report)", STOC 1973, 1-9, doi:10.1145/800125.804029).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ReynoldsCoveringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering

/-- A right-hand side of Garey and Johnson's regular form: a terminal followed by a nonterminal
(`a B`), or a single terminal (`a`). -/
def isRegularRhs : List (Bool × ℕ) → Bool
  | [(true, _)] => true
  | [(true, _), (false, _)] => true
  | _ => false

/-- A grammar is regular when every production is `A → a B` or `A → a`. -/
def IsRegularGrammar (g : GrammarData) : Prop :=
  ∀ p ∈ g.2.2, isRegularRhs p.2 = true

/-- Well-formedness of an instance: both grammars are well-formed over the terminal alphabet
`{0, …, k - 1}` and regular, and the alphabet has exactly one letter. -/
def WellFormed (i : ReynoldsCoveringInstance) : Prop :=
  GrammarWellFormed i.1 i.2.1 ∧ GrammarWellFormed i.1 i.2.2 ∧ IsRegularGrammar i.2.1 ∧
    IsRegularGrammar i.2.2 ∧ i.1 = 1

/-- `G₁` and `G₂` generate different languages. -/
def RegularGrammarInequivalenceFeasible (i : ReynoldsCoveringInstance) : Prop :=
  (toEncodedCFG i.2.1).language ≠ (toEncodedCFG i.2.2).language

open Classical in
/-- REGULAR GRAMMAR INEQUIVALENCE over a one-letter alphabet as a decision problem over
bitstrings. -/
noncomputable def regularGrammarInequivalenceUnaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCoveringInstance) x with
  | some i => decide (WellFormed i ∧ RegularGrammarInequivalenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary
