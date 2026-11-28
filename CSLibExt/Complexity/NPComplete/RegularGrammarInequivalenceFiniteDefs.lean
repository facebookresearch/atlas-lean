/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR GRAMMAR INEQUIVALENCE for finite languages: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL14] REGULAR GRAMMAR INEQUIVALENCE,
p. 269, comment: the general problem is NP-complete "if both grammars generate finite languages
(a property that can be checked in polynomial time)" (no separate citation; the related [AL9]
comment, p. 267, records that REGULAR EXPRESSION INEQUIVALENCE is NP-complete for star-free
expressions, which denote finite languages, citing L. J. Stockmeyer and A. R. Meyer, "Word
problems requiring exponential time (preliminary report)", STOC 1973, 1-9,
doi:10.1145/800125.804029).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Finite.Defs
public import CSLibExt.Complexity.NPComplete.ReynoldsCoveringDefs
public import CSLibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceFinite

open MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
open MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceUnary

/-- Well-formedness of an instance: both grammars are well-formed over the terminal alphabet
`{0, …, k - 1}` and regular, and both generate finite languages. -/
def WellFormed (i : ReynoldsCoveringInstance) : Prop :=
  GrammarWellFormed i.1 i.2.1 ∧ GrammarWellFormed i.1 i.2.2 ∧ IsRegularGrammar i.2.1 ∧
    IsRegularGrammar i.2.2 ∧ Set.Finite (toEncodedCFG i.2.1).language ∧
      Set.Finite (toEncodedCFG i.2.2).language

open Classical in
/-- REGULAR GRAMMAR INEQUIVALENCE for finite languages as a decision problem over bitstrings. -/
noncomputable def regularGrammarInequivalenceFiniteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCoveringInstance) x with
  | some i => decide (WellFormed i ∧ RegularGrammarInequivalenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegularGrammarInequivalenceFinite
