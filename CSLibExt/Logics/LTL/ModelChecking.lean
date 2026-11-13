/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.FullBuchi
public import CSLibExt.Computability.Automata.NA.BuchiEmptiness

/-!
# Full-LTL model checking by a Büchi product

The model is the canonical `Cslib.LTS`. Formula valuations are on model states,
not on transition actions. A product consumes the current state as its input
letter and synchronizes a real model transition with a recognizer transition.

Counterexamples are infinite canonical executions satisfying the negated
formula. For finite models they exist exactly when the product has a reachable
accepting nonempty cycle, using the existing proved Büchi emptiness theorem.
No seriality is assumed. A deadlocked initial state has no infinite execution;
this is not a theorem about maximal finite paths or deadlock completion.
-/

@[expose] public section

namespace Cslib.LTL.ModelChecking

open Automata.NA Automata.ωAcceptor

variable {State Action Atom Q : Type*}

/-- An initial infinite state run, witnessed by a canonical action execution. -/
def IsRun (lts : LTS State Action) (initial : Set State)
    (w : ωSequence State) : Prop :=
  w 0 ∈ initial ∧ ∃ actions : ωSequence Action, lts.OmegaExecution w actions

/-- Equivalently, every adjacent state pair has a real model transition. -/
theorem isRun_iff (lts : LTS State Action) (initial : Set State)
    (w : ωSequence State) :
    IsRun lts initial w ↔ w 0 ∈ initial ∧
      ∀ n, ∃ action, lts.Tr (w n) action (w (n + 1)) := by
  constructor
  · rintro ⟨hstart, actions, hexec⟩
    exact ⟨hstart, fun n => ⟨actions n, hexec n⟩⟩
  · rintro ⟨hstart, hsteps⟩
    classical
    choose actions hexec using hsteps
    exact ⟨hstart, actions, hexec⟩

/-- Synchronized state-reading product, with the recognizer's Büchi condition. -/
def product (lts : LTS State Action) (initial : Set State)
    (a : Buchi Q State) : Buchi (State × Q) State where
  Tr p x q := x = p.1 ∧ (∃ action, lts.Tr p.1 action q.1) ∧ a.Tr p.2 x q.2
  start := {p | p.1 ∈ initial ∧ p.2 ∈ a.start}
  accept := {p | p.2 ∈ a.accept}

/-- A product accepts precisely the model runs accepted by its recognizer. -/
theorem mem_product_iff (lts : LTS State Action) (initial : Set State)
    (a : Buchi Q State) (w : ωSequence State) :
    w ∈ language (product lts initial a) ↔ IsRun lts initial w ∧ w ∈ language a := by
  rw [isRun_iff]
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    have heq : ∀ n, w n = (ss n).1 := fun n => (hrun.trans n).1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [heq 0] using hrun.start.1
    · intro n
      simpa only [heq n, heq (n + 1)] using (hrun.trans n).2.1
    · exact ⟨fun n => (ss n).2,
        ⟨hrun.start.2, fun n => (hrun.trans n).2.2⟩, hacc⟩
  · rintro ⟨⟨hstart, hsteps⟩, ss, hrun, hacc⟩
    exact ⟨fun n => (w n, ss n),
      ⟨⟨hstart, hrun.start⟩, fun n => ⟨rfl, hsteps n, hrun.trans n⟩⟩, hacc⟩

/-- The finite-state product for runs that violate the full LTL formula. -/
def counterexample (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Buchi (State × (Tableau.State (.not φ) ×
      Fin (Tableau.obligationCount (.not φ) + 1))) State :=
  product lts initial (Tableau.buchi valuation (.not φ))

/-- All initial infinite canonical executions satisfy the formula. -/
def Models (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) : Prop :=
  ∀ w : ωSequence State, IsRun lts initial w → Word.Satisfies valuation w φ

/-- A counterexample word is exactly an infinite model run violating LTL. -/
theorem mem_counterexample_iff (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) (w : ωSequence State) :
    w ∈ language (counterexample lts initial valuation φ) ↔
      IsRun lts initial w ∧ ¬ Word.Satisfies valuation w φ := by
  change w ∈ language (product lts initial (Tableau.buchi valuation (.not φ))) ↔ _
  rw [mem_product_iff, Tableau.mem_buchi_iff, Word.Satisfies.not_iff]

/-- Full-LTL model checking reduces to the proved finite Büchi lasso criterion.
A cycle must be nonempty; neither seriality nor finite action/atom types are needed. -/
theorem models_iff_no_lasso [Finite State] (lts : LTS State Action)
    (initial : Set State) (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Models lts initial valuation φ ↔
      ¬ (counterexample lts initial valuation φ).HasLasso := by
  rw [← Buchi.language_nonempty_iff_hasLasso]
  constructor
  · intro h ⟨w, hw⟩
    obtain ⟨hrun, hnot⟩ := (mem_counterexample_iff lts initial valuation φ w).mp hw
    exact hnot (h w hrun)
  · intro h w hrun
    by_contra hnot
    exact h ⟨w, (mem_counterexample_iff lts initial valuation φ w).mpr ⟨hrun, hnot⟩⟩

/-- Universal infinite-run satisfaction is emptiness of the counterexample language. -/
theorem models_iff_language_empty (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Models lts initial valuation φ ↔
      language (counterexample lts initial valuation φ) = ⊥ := by
  constructor
  · intro h
    apply ωLanguage.mem_ext
    intro w
    change w ∈ language (counterexample lts initial valuation φ) ↔ False
    refine ⟨fun hw => ?_, False.elim⟩
    obtain ⟨hrun, hnot⟩ := (mem_counterexample_iff lts initial valuation φ w).mp hw
    exact hnot (h w hrun)
  · intro h w hrun
    by_contra hnot
    have hw := (mem_counterexample_iff lts initial valuation φ w).mpr ⟨hrun, hnot⟩
    rw [h] at hw
    exact hw

end Cslib.LTL.ModelChecking
