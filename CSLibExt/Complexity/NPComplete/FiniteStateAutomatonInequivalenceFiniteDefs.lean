/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE STATE AUTOMATON INEQUIVALENCE for finite languages: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL1] FINITE STATE AUTOMATON
INEQUIVALENCE, p. 265, comment: the general problem is NP-complete "if `A₁` and `A₂` both
recognize finite languages (a property that can be checked in polynomial time)" (no separate
citation; the related [AL9] comment, p. 267, records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete for star-free expressions, which denote finite languages, citing L. J. Stockmeyer
and A. R. Meyer, "Word problems requiring exponential time (preliminary report)", STOC 1973,
1-9, doi:10.1145/800125.804029).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Finite.Defs
public import CSLibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceFinite

open MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary

/-- Well-formedness of an instance: both automata are well-formed over the alphabet
`{0, …, m - 1}`, and both recognize finite languages. -/
def WellFormed (i : AutomatonInequivalenceInstance) : Prop :=
  AutomatonWellFormed i.1 i.2.1 ∧ AutomatonWellFormed i.1 i.2.2 ∧
    Set.Finite (toEncodedNFA i.2.1).language ∧ Set.Finite (toEncodedNFA i.2.2).language

open Classical in
/-- FINITE STATE AUTOMATON INEQUIVALENCE for finite languages as a decision problem over
bitstrings. -/
noncomputable def automatonInequivalenceFiniteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AutomatonInequivalenceInstance) x with
  | some i => decide (WellFormed i ∧ AutomatonInequivalenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceFinite
