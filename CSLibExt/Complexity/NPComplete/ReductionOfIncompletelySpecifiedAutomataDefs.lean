/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL7] REDUCTION OF
INCOMPLETELY SPECIFIED AUTOMATA;
C. P. Pfleeger, "State reduction in incompletely specified finite-state
machines", IEEE Transactions on Computers C-22 (1973), 1099-1102,
doi:10.1109/T-C.1973.223655.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Computability.DFA

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata

/-- An instance: state count `n` (states `Fin n`), alphabet size `m` (letters `Fin m`), the
specified transitions `((q, a), q')`, start state `q₀`, accept states `F`, bound `K`. -/
abbrev ReductionOfIncompletelySpecifiedAutomataInstance :=
  ℕ × ℕ × List ((ℕ × ℕ) × ℕ) × ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: every listed transition has its state, letter and target in
range, no state-letter pair has two different targets, the start state and the accept states are
in range, and `K` is positive. -/
def WellFormed (i : ReductionOfIncompletelySpecifiedAutomataInstance) : Prop :=
  (∀ t ∈ i.2.2.1, t.1.1 < i.1 ∧ t.1.2 < i.2.1 ∧ t.2 < i.1) ∧
    (∀ t ∈ i.2.2.1, ∀ t' ∈ i.2.2.1, t.1 = t'.1 → t.2 = t'.2) ∧
    i.2.2.2.1 < i.1 ∧ (∀ f ∈ i.2.2.2.2.1, f < i.1) ∧ 0 < i.2.2.2.2.2

/-- A total transition function `d` extends the specified transitions: `d q a = q'` for every
listed entry `((q, a), q')`. -/
def Extends (i : ReductionOfIncompletelySpecifiedAutomataInstance)
    (d : Fin i.1 → Fin i.2.1 → Fin i.1) : Prop :=
  ∀ q : Fin i.1, ∀ a : Fin i.2.1, ∀ q' : ℕ, (((q : ℕ), (a : ℕ)), q') ∈ i.2.2.1 → (d q a : ℕ) = q'

/-- The completely specified automaton with transition function `d`, start state `s` and the
instance's accept states. -/
def completion (i : ReductionOfIncompletelySpecifiedAutomataInstance)
    (d : Fin i.1 → Fin i.2.1 → Fin i.1) (s : Fin i.1) : DFA (Fin i.2.1) (Fin i.1) where
  step := d
  start := s
  accept := {q | (q : ℕ) ∈ i.2.2.2.2.1}

/-- Some extension `d` of the specified transitions yields an automaton whose language is
accepted by a `DFA` with `k ≤ K` states. -/
def ReductionOfIncompletelySpecifiedAutomataFeasible
    (i : ReductionOfIncompletelySpecifiedAutomataInstance) : Prop :=
  ∃ hq : i.2.2.2.1 < i.1, ∃ d : Fin i.1 → Fin i.2.1 → Fin i.1, Extends i d ∧
    ∃ k ≤ i.2.2.2.2.2, ∃ B : DFA (Fin i.2.1) (Fin k),
      B.accepts = (completion i d ⟨i.2.2.2.1, hq⟩).accepts

open Classical in
/-- REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA as a decision problem over bitstrings. -/
noncomputable def reductionOfIncompletelySpecifiedAutomataDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReductionOfIncompletelySpecifiedAutomataInstance) x with
  | some i => decide (WellFormed i ∧ ReductionOfIncompletelySpecifiedAutomataFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata
