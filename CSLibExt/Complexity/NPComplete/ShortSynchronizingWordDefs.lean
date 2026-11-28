/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORT SYNCHRONIZING WORD: definitions

Source:
D. Eppstein, "Reset sequences for monotonic automata", SIAM Journal on Computing 19(3) (1990),
500-510, doi:10.1137/0219033, Theorem 8 (given an automaton and an integer `m`, deciding
whether the automaton has a reset sequence of length at most `m` is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortSynchronizingWord

/-- An instance: the number of states `n` (states `Fin n`), the alphabet size `k` (letters
`Fin k`), the transition table (row `q` lists `δ(q, a)` for each letter `a`), and the bound
`m`. -/
abbrev ShortSynchronizingWordInstance := ℕ × ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the table has one row per state, every row has one entry
per letter, and every entry is a state (below `n`). -/
def WellFormed (i : ShortSynchronizingWordInstance) : Prop :=
  i.2.2.1.length = i.1 ∧ ∀ row ∈ i.2.2.1, row.length = i.2.1 ∧ ∀ s ∈ row, s < i.1

/-- The automaton as a functional labelled transition system: `δ(q, a)` is row `q`, entry `a`
of the table. On well-formed instances every entry is below `n`, so the reduction modulo `n`
(which only makes the value a state) leaves it unchanged. -/
def automaton (i : ShortSynchronizingWordInstance) : Cslib.FLTS (Fin i.1) (Fin i.2.1) where
  tr q a := ⟨((i.2.2.1.getD q.val []).getD a.val 0) % i.1, Nat.mod_lt _ q.pos⟩

/-- Some word `τ` with `|τ| ≤ m` is a reset sequence: the set `δ(τ, S)` of the states reached
from all states `s ∈ S` has exactly one element. -/
def ShortSynchronizingWordFeasible (i : ShortSynchronizingWordInstance) : Prop :=
  ∃ τ : List (Fin i.2.1), τ.length ≤ i.2.2.2 ∧
    (Finset.univ.image fun s : Fin i.1 => (automaton i).mtr s τ).card = 1

open Classical in
/-- SHORT SYNCHRONIZING WORD as a decision problem over bitstrings. -/
noncomputable def shortSynchronizingWordDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortSynchronizingWordInstance) x with
  | some i => decide (WellFormed i ∧ ShortSynchronizingWordFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortSynchronizingWord
