/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE STATE AUTOMATON INEQUIVALENCE over a one-letter alphabet: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL1] FINITE STATE AUTOMATON
INEQUIVALENCE, p. 265, comment: the general problem is NP-complete if `|Σ| = 1` (no separate
citation; the related [AL9] comment records that REGULAR EXPRESSION INEQUIVALENCE is
NP-complete if `|Σ| = 1`, citing L. J. Stockmeyer and A. R. Meyer, "Word problems requiring
exponential time (preliminary report)", STOC 1973, 1-9, doi:10.1145/800125.804029).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Automata.NA.EncodedNFA

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary

/-- An automaton as data: the number `n` of states, the initial state, the accept states, and
the transitions `((s, a), t)`. -/
abbrev AutomatonData := ℕ × ℕ × List ℕ × List ((ℕ × ℕ) × ℕ)

/-- An instance: the alphabet size `m` (letters `0, …, m - 1`) and the automata `A₁`, `A₂`. -/
abbrev AutomatonInequivalenceInstance := ℕ × AutomatonData × AutomatonData

/-- The automaton as a CSLibExt `EncodedNFA`: start state `q₀`, the accept states, the
transitions, and no ε-moves. -/
def toEncodedNFA (A : AutomatonData) : Cslib.Automata.EncodedNFA ℕ :=
  ⟨[A.2.1], A.2.2.1, A.2.2.2, []⟩

/-- An automaton is well-formed over `m` letters when its initial state, its accept states and
the endpoints of its transitions are among its `n` states, and every transition letter is below
`m`. -/
def AutomatonWellFormed (m : ℕ) (A : AutomatonData) : Prop :=
  A.2.1 < A.1 ∧ (∀ q ∈ A.2.2.1, q < A.1) ∧
    ∀ e ∈ A.2.2.2, e.1.1 < A.1 ∧ e.1.2 < m ∧ e.2 < A.1

/-- Well-formedness of an instance: both automata are well-formed over the alphabet, and the
alphabet has exactly one letter. -/
def WellFormed (i : AutomatonInequivalenceInstance) : Prop :=
  AutomatonWellFormed i.1 i.2.1 ∧ AutomatonWellFormed i.1 i.2.2 ∧ i.1 = 1

/-- `A₁` and `A₂` recognize different languages. -/
def AutomatonInequivalenceFeasible (i : AutomatonInequivalenceInstance) : Prop :=
  (toEncodedNFA i.2.1).language ≠ (toEncodedNFA i.2.2).language

open Classical in
/-- FINITE STATE AUTOMATON INEQUIVALENCE over a one-letter alphabet as a decision problem over
bitstrings. -/
noncomputable def automatonInequivalenceUnaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AutomatonInequivalenceInstance) x with
  | some i => decide (WellFormed i ∧ AutomatonInequivalenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiniteStateAutomatonInequivalenceUnary
