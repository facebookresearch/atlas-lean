/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL7] REDUCTION OF
INCOMPLETELY SPECIFIED AUTOMATA;
C. P. Pfleeger, "State reduction in incompletely specified finite-state
machines", IEEE Transactions on Computers C-22 (1973), 1099-1102,
doi:10.1109/T-C.1973.223655.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Computability.DFA

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata

/-!
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete

INSTANCE: an incompletely specified deterministic finite state automaton
`A = (Q, Σ, δ, q₀, F)`, whose transition function `δ` maps a subset of `Q × Σ` into `Q`, and a
positive integer `K`. QUESTION: can `δ` be extended to a total function `Q × Σ → Q` so that the
resulting completely specified automaton has an equivalent reduced automaton with `K` or fewer
states?

The states are `Fin n` and the alphabet is `Fin m`. The partial transition function is a list of
entries `((q, a), q')`, read as `δ(q, a) = q'`; `WellFormed` requires the list to be functional.
A completion is a total `d : Fin n → Fin m → Fin n` that agrees with every listed entry; it
gives the Mathlib `DFA` `completion i d q₀`. Two automata are equivalent when they accept the same
language, so the completed automaton has an equivalent reduced (minimum-state) automaton with at
most `K` states exactly when some `DFA` with at most `K` states accepts its language.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete.** Source: Garey and Johnson
(1979), [AL7]; Pfleeger (1973). -/
public theorem_wanted reductionOfIncompletelySpecifiedAutomata_npComplete :
    reductionOfIncompletelySpecifiedAutomataDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reductionOfIncompletelySpecifiedAutomataDec

end MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata
