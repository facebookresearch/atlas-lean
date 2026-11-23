/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.OmegaWord
public import CSLibExt.Computability.Automata.NA.GeneralizedBuchi

/-!
# Finite truth-annotation tableaux for full LTL

There is one Boolean per syntactic occurrence, not per atom. This keeps
states finite without requiring a finite or decidable atom type. Transitions
check local Boolean and temporal expansion equations; each until occurrence
has its own fairness requirement, excluding infinite postponement.

The construction follows the truth-annotation form of the LTL tableau
argument of Vardi and Wolper, LICS 1986. No external Lean code is copied.
-/

@[expose] public section

namespace Cslib.LTL.Tableau

variable {Atom Symbol : Type*}

/-- One Boolean for each syntactic occurrence in an LTL formula. -/
@[reducible]
def State : Formula Atom → Type
  | .atom _ => Bool
  | .top => Bool
  | .not φ => Bool × State φ
  | .and φ ψ => Bool × (State φ × State ψ)
  | .next φ => Bool × State φ
  | .until φ ψ => Bool × (State φ × State ψ)

/-- The state carrier is enumerable, independently of the atom type. -/
instance stateFintype : (φ : Formula Atom) → Fintype (State φ)
  | .atom _ => inferInstanceAs (Fintype Bool)
  | .top => inferInstanceAs (Fintype Bool)
  | .not φ => by
      letI := stateFintype φ
      exact inferInstanceAs (Fintype (Bool × State φ))
  | .and φ ψ => by
      letI := stateFintype φ
      letI := stateFintype ψ
      exact inferInstanceAs (Fintype (Bool × (State φ × State ψ)))
  | .next φ => by
      letI := stateFintype φ
      exact inferInstanceAs (Fintype (Bool × State φ))
  | .until φ ψ => by
      letI := stateFintype φ
      letI := stateFintype ψ
      exact inferInstanceAs (Fintype (Bool × (State φ × State ψ)))

/-- Equality of annotations is decidable without comparing atoms. -/
instance stateDecidableEq : (φ : Formula Atom) → DecidableEq (State φ)
  | .atom _ => inferInstanceAs (DecidableEq Bool)
  | .top => inferInstanceAs (DecidableEq Bool)
  | .not φ => by
      letI := stateDecidableEq φ
      exact inferInstanceAs (DecidableEq (Bool × State φ))
  | .and φ ψ => by
      letI := stateDecidableEq φ
      letI := stateDecidableEq ψ
      exact inferInstanceAs (DecidableEq (Bool × (State φ × State ψ)))
  | .next φ => by
      letI := stateDecidableEq φ
      exact inferInstanceAs (DecidableEq (Bool × State φ))
  | .until φ ψ => by
      letI := stateDecidableEq φ
      letI := stateDecidableEq ψ
      exact inferInstanceAs (DecidableEq (Bool × (State φ × State ψ)))

/-- The truth bit at the root of an annotation. -/
def value : (φ : Formula Atom) → State φ → Bool
  | .atom _, s => s
  | .top, s => s
  | .not _, s => s.1
  | .and _ _, s => s.1
  | .next _, s => s.1
  | .until _ _, s => s.1

/-- The number of until occurrences, hence of fairness requirements. -/
def obligationCount : Formula Atom → ℕ
  | .atom _ => 0
  | .top => 0
  | .not φ => obligationCount φ
  | .and φ ψ => obligationCount φ + obligationCount ψ
  | .next φ => obligationCount φ
  | .until φ ψ => obligationCount φ + obligationCount ψ + 1

/-- Local equations at every occurrence. The symbol labels the source state. -/
def step (valuation : Symbol → Atom → Prop) :
    (φ : Formula Atom) → State φ → Symbol → State φ → Prop
  | .atom a, s, x, _ => s = true ↔ valuation x a
  | .top, s, _, _ => s = true
  | .not φ, s, x, t =>
      (s.1 = true ↔ ¬ value φ s.2 = true) ∧
        step valuation φ s.2 x t.2
  | .and φ ψ, s, x, t =>
      (s.1 = true ↔ value φ s.2.1 = true ∧ value ψ s.2.2 = true) ∧
        step valuation φ s.2.1 x t.2.1 ∧
        step valuation ψ s.2.2 x t.2.2
  | .next φ, s, x, t =>
      (s.1 = true ↔ value φ t.2 = true) ∧
        step valuation φ s.2 x t.2
  | .until φ ψ, s, x, t =>
      (s.1 = true ↔ value ψ s.2.2 = true ∨
        (value φ s.2.1 = true ∧ t.1 = true)) ∧
        step valuation φ s.2.1 x t.2.1 ∧
        step valuation ψ s.2.2 x t.2.2

/-- The Boolean test for each until fairness requirement. -/
def obligation : (φ : Formula Atom) →
    Fin (obligationCount φ) → State φ → Bool
  | .atom _, i, _ => Fin.elim0 i
  | .top, i, _ => Fin.elim0 i
  | .not φ, i, s => obligation φ i s.2
  | .and φ ψ, i, s =>
      Fin.addCases (fun j => obligation φ j s.2.1)
        (fun j => obligation ψ j s.2.2) i
  | .next φ, i, s => obligation φ i s.2
  | .until φ ψ, i, s =>
      Fin.cases (!s.1 || value ψ s.2.2)
        (Fin.addCases (fun j => obligation φ j s.2.1)
          (fun j => obligation ψ j s.2.2)) i

open Filter

/-- Every until occurrence is absent or fulfilled at arbitrarily late times. -/
def Fair : (φ : Formula Atom) → ωSequence (State φ) → Prop
  | .atom _, _ => True
  | .top, _ => True
  | .not φ, ss => Fair φ (fun n => (ss n).2)
  | .and φ ψ, ss =>
      Fair φ (fun n => (ss n).2.1) ∧ Fair ψ (fun n => (ss n).2.2)
  | .next φ, ss => Fair φ (fun n => (ss n).2)
  | .until φ ψ, ss =>
      (∃ᶠ n in atTop, (ss n).1 = false ∨ value ψ (ss n).2.2 = true) ∧
        Fair φ (fun n => (ss n).2.1) ∧ Fair ψ (fun n => (ss n).2.2)

/-- Generalized Büchi tableau: the root is initially true. -/
def automaton (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    Automata.NA.GenBuchi (State φ) Symbol where
  Tr := step valuation φ
  start := {s | value φ s = true}
  k := obligationCount φ
  accept i := {s | obligation φ i s = true}

/-- Structural fairness is exactly generalized Büchi acceptance. -/
theorem fair_iff (φ : Formula Atom) (ss : ωSequence (State φ)) :
    Fair φ ss ↔ ∀ i, ∃ᶠ n in atTop, obligation φ i (ss n) = true := by
  induction φ with
  | atom a => simp [Fair, obligationCount]
  | top => simp [Fair, obligationCount]
  | not φ ih =>
      simpa only [Fair, obligation, obligationCount, ωSequence.get_fun]
        using ih (fun n => (ss n).2)
  | and φ ψ ihφ ihψ =>
      simpa [Fair, obligationCount, obligation, Fin.forall_fin_add,
        ωSequence.get_fun] using
        and_congr (ihφ (fun n => (ss n).2.1))
          (ihψ (fun n => (ss n).2.2))
  | next φ ih =>
      simpa only [Fair, obligation, obligationCount, ωSequence.get_fun]
        using ih (fun n => (ss n).2)
  | «until» φ ψ ihφ ihψ =>
      simp only [Fair, frequently_or_distrib, obligationCount, obligation,
        Fin.forall_fin_succ, Fin.cases_zero, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, Fin.cases_succ,
        Fin.forall_fin_add, Fin.addCases_left, Fin.addCases_right,
        and_congr_right_iff]
      intro _
      simpa only [ωSequence.get_fun] using
        and_congr (ihφ (fun n => (ss n).2.1))
          (ihψ (fun n => (ss n).2.2))

open Automata.ωAcceptor

/-- Membership exposes exactly the initial, local, and fairness conditions. -/
theorem mem_language_iff (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) (w : ωSequence Symbol) :
    w ∈ language (automaton valuation φ) ↔
      ∃ ss : ωSequence (State φ), value φ (ss 0) = true ∧
        (∀ n, step valuation φ (ss n) (w n) (ss (n + 1))) ∧
        Fair φ ss := by
  rw [Automata.NA.GenBuchi.mem_language_iff]
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    exact ⟨ss, hrun.start, hrun.trans, (fair_iff φ ss).mpr hacc⟩
  · rintro ⟨ss, hstart, hstep, hfair⟩
    exact ⟨ss, ⟨hstart, hstep⟩, (fair_iff φ ss).mp hfair⟩

end Cslib.LTL.Tableau
