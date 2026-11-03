/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Name-scoping transport is adapted from Meta's finite-session typing
development in this project, under the same Meta license. The exact source
is preserved in `docs/provenance/pi-scoping/finite-session-basic.lean.txt`;
`docs/provenance/pi-scoping/manifest.json` records its origin path/revision,
declaration locations, SHA-256, and the adaptations made here.
The shared interface generalizes name lifting to arbitrary cutoffs and
retains the source's name-substitution hypotheses. Process scoping and
lifting-identity lemmas are shared with the π contextual theory.
-/

module

public import CSLibExt.Languages.PiCalculus.Basic
import Batteries.Logic

/-!
# Scope preservation for π-calculus names and processes

The shared name predicate counts surrounding input/restriction binders;
free constants are always in scope. `Proc.ClosedAt 0` permits free channels
but excludes dangling de Bruijn variables. This module depends only on the
existing π syntax and substitution, not its behavioural/contextual theory.
-/

@[expose] public section

namespace Cslib.PiCalculus

/-- A name refers only to the `depth` surrounding binders or to a free
constant. At depth zero, no variable is permitted. -/
def Name.ClosedAt (depth : ℕ) : Name → Prop
  | .const _ => True
  | .var i => i < depth

/-- Every variable refers to an enclosing input/restriction binder.
`ClosedAt 0` permits free constants, but no dangling de Bruijn variables. -/
def Proc.ClosedAt (depth : ℕ) : Proc → Prop
  | .nil => True
  | .out a b p =>
      a.ClosedAt depth ∧ b.ClosedAt depth ∧ Proc.ClosedAt depth p
  | .inp a p => a.ClosedAt depth ∧ Proc.ClosedAt (depth + 1) p
  | .par p q => Proc.ClosedAt depth p ∧ Proc.ClosedAt depth q
  | .nu p => Proc.ClosedAt (depth + 1) p
  | .repl p => Proc.ClosedAt depth p
  | .sum p q => Proc.ClosedAt depth p ∧ Proc.ClosedAt depth q

/-- Lifting above the ambient binder depth fixes an in-scope name. -/
theorem liftName_eq_of_closedAt {a : Name} {k : ℕ}
    (h : a.ClosedAt k) : liftName k a = a := by
  cases a with
  | const => rfl
  | var i => simp [liftName, Nat.not_le_of_lt h]

/-- Lifting above the surrounding binders fixes a locally closed process.
At depth zero, insertion under a fresh binder cannot capture its names. -/
theorem liftProc_eq_of_closedAt {p : Proc} {k : ℕ}
    (h : Proc.ClosedAt k p) : liftProc k p = p := by
  induction p generalizing k with
  | nil => rfl
  | out a b p ih =>
    simp only [liftProc, liftName_eq_of_closedAt h.1,
      liftName_eq_of_closedAt h.2.1, ih h.2.2]
  | inp a p ih =>
    exact congrArg₂ Proc.inp (liftName_eq_of_closedAt h.1) (ih h.2)
  | par p q ihp ihq => exact congrArg₂ Proc.par (ihp h.1) (ihq h.2)
  | nu p ih => exact congrArg Proc.nu (ih h)
  | repl p ih => exact congrArg Proc.repl (ih h)
  | sum p q ihp ihq => exact congrArg₂ Proc.sum (ihp h.1) (ihq h.2)

/-- Inserting a binder at any cutoff preserves name scoping in the
larger environment. -/
theorem Name.ClosedAt.lift {n k : ℕ} {b : Name} (h : b.ClosedAt n) :
    (liftName k b).ClosedAt (n + 1) := by
  cases b with
  | const => trivial
  | var i =>
    change i < n at h
    by_cases hk : k ≤ i
    · simpa only [liftName, hk, ↓reduceIte, Name.ClosedAt] using
        Nat.add_lt_add_right h 1
    · simpa only [liftName, hk, ↓reduceIte, Name.ClosedAt] using
        Nat.lt_succ_of_lt h

/-- Removing the binder at `k ≤ n` preserves name scoping when its
replacement is scoped in the remaining environment. -/
theorem Name.ClosedAt.subst {n k : ℕ} {b x : Name}
    (hb : b.ClosedAt n) (hx : x.ClosedAt (n + 1)) (hk : k ≤ n) :
    (substName b k x).ClosedAt n := by
  cases x with
  | const => trivial
  | var i =>
    simp only [substName]
    split
    · simp only [Name.ClosedAt] at *
      omega
    · split
      · exact hb
      · simp only [Name.ClosedAt] at *
        omega

/-- Shifting a process past a new binder preserves scoping. Inner input
and restriction binders increase the cutoff as in `Basic.liftProc`. -/
theorem Proc.ClosedAt.lift {p : Proc} {n k : ℕ}
    (h : p.ClosedAt n) : (liftProc k p).ClosedAt (n + 1) := by
  induction p generalizing n k with
  | nil => trivial
  | out a b p ih => exact ⟨h.1.lift, h.2.1.lift, ih h.2.2⟩
  | inp a p ih => exact ⟨h.1.lift, ih h.2⟩
  | par p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | nu p ih => exact ih h
  | repl p ih => exact ih h
  | sum p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩

/-- Capture-avoiding substitution removes one ambient binder while
preserving every name's scope, including under input and restriction. -/
theorem Proc.ClosedAt.substProc {p : Proc} {n k : ℕ} {b : Name}
    (h : p.ClosedAt (n + 1)) (hb : b.ClosedAt n) (hk : k ≤ n) :
    (PiCalculus.substProc b k p).ClosedAt n := by
  induction p generalizing n k b with
  | nil => trivial
  | out a x p ih =>
    exact ⟨hb.subst h.1 hk, hb.subst h.2.1 hk, ih h.2.2 hb hk⟩
  | inp a p ih =>
    exact ⟨hb.subst h.1 hk,
      ih h.2 hb.lift (Nat.add_le_add_right hk 1)⟩
  | par p q ihp ihq => exact ⟨ihp h.1 hb hk, ihq h.2 hb hk⟩
  | nu p ih => exact ih h hb.lift (Nat.add_le_add_right hk 1)
  | repl p ih => exact ih h hb hk
  | sum p q ihp ihq => exact ⟨ihp h.1 hb hk, ihq h.2 hb hk⟩

/-- Instantiating the innermost binder preserves process scoping. -/
theorem Proc.ClosedAt.subst {p : Proc} {n : ℕ} {b : Name}
    (h : p.ClosedAt (n + 1)) (hb : b.ClosedAt n) :
    (PiCalculus.subst p b).ClosedAt n :=
  h.substProc hb (Nat.zero_le n)

end Cslib.PiCalculus
