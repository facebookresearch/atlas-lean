/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.ModelChecking

/-!
# Executable full-LTL model checking

The semantic recognizer permits arbitrary Prop valuations. Executing a checker
additionally requires actual decision procedures for the model transitions,
initial set and valuation, and enumerations of model states and actions.
Atoms still need neither enumeration nor decidable equality.

The generic degeneralization counter is noncomputable for arbitrary accept
sets. Here its tests are explicit Booleans. A computational counter update is
proved equal to the generic one, so actual decidability instances execute the
existing Büchi emptiness algorithm without an assumed oracle or a new automaton.
-/

@[expose] public section

namespace Cslib.LTL.Tableau

variable {Atom Symbol : Type*}

/-- Local tableau transitions are decidable with a decidable valuation. -/
instance stepDecidable (valuation : Symbol → Atom → Prop)
    [∀ x a, Decidable (valuation x a)] :
    (φ : Formula Atom) → (s : State φ) → (x : Symbol) → (t : State φ) →
      Decidable (step valuation φ s x t)
  | .atom a, s, x, _ => by
      dsimp only [State] at s
      exact inferInstanceAs (Decidable (s = true ↔ valuation x a))
  | .top, s, _, _ => by
      dsimp only [State] at s
      exact inferInstanceAs (Decidable (s = true))
  | .not φ, s, x, t => by
      letI := stepDecidable valuation φ s.2 x t.2
      dsimp only [step]
      infer_instance
  | .and φ ψ, s, x, t => by
      letI := stepDecidable valuation φ s.2.1 x t.2.1
      letI := stepDecidable valuation ψ s.2.2 x t.2.2
      dsimp only [step]
      infer_instance
  | .next φ, s, x, t => by
      letI := stepDecidable valuation φ s.2 x t.2
      dsimp only [step]
      infer_instance
  | .until φ ψ, s, x, t => by
      letI := stepDecidable valuation φ s.2.1 x t.2.1
      letI := stepDecidable valuation ψ s.2.2 x t.2.2
      dsimp only [step]
      infer_instance

/-- Computable fairness-counter update, reading the destination annotation. -/
def advance (φ : Formula Atom) (i : Fin (obligationCount φ + 1)) (t : State φ) :
    Fin (obligationCount φ + 1) :=
  if h : i.val < obligationCount φ then
    if obligation φ ⟨i.val, h⟩ t = true then ⟨i.val + 1, by omega⟩ else i
  else ⟨0, Nat.zero_lt_succ _⟩

/-- The computable update is exactly the existing generic degeneralization. -/
theorem nextCount_eq_advance (valuation : Symbol → Atom → Prop) (φ : Formula Atom)
    (i : Fin (obligationCount φ + 1)) (t : State φ) :
    (automaton valuation φ).nextCount i t = advance φ i t := by
  by_cases h : i.val < obligationCount φ
  · by_cases ht : obligation φ ⟨i.val, h⟩ t = true
    · simp [Automata.NA.GenBuchi.nextCount, advance, automaton, h, ht]
    · simp [Automata.NA.GenBuchi.nextCount, advance, automaton, h, ht]
  · simp [Automata.NA.GenBuchi.nextCount, advance, automaton, h]

/-- The existing Büchi transition can be tested using the computable update. -/
theorem buchi_tr_iff (valuation : Symbol → Atom → Prop) (φ : Formula Atom)
    (p : State φ × Fin (obligationCount φ + 1)) (x : Symbol)
    (q : State φ × Fin (obligationCount φ + 1)) :
    (buchi valuation φ).Tr p x q ↔
      step valuation φ p.1 x q.1 ∧ q.2 = advance φ p.2 q.1 :=
  and_congr Iff.rfl (Iff.of_eq (congrArg (fun j => q.2 = j)
    (nextCount_eq_advance valuation φ p.2 q.1)))

/-- Decidability uses the Boolean counter update, not classical membership. -/
instance buchiTrDecidable (valuation : Symbol → Atom → Prop)
    [∀ x a, Decidable (valuation x a)] (φ : Formula Atom)
    (p : State φ × Fin (obligationCount φ + 1)) (x : Symbol)
    (q : State φ × Fin (obligationCount φ + 1)) :
    Decidable ((buchi valuation φ).Tr p x q) :=
  decidable_of_iff (step valuation φ p.1 x q.1 ∧ q.2 = advance φ p.2 q.1)
    (buchi_tr_iff valuation φ p x q).symm

/-- The initial counter and root bit are decidable. -/
instance buchiStartDecidable (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) : DecidablePred (· ∈ (buchi valuation φ).start) :=
  fun p => inferInstanceAs (Decidable
    (value φ p.1 = true ∧ p.2 = (⟨0, Nat.zero_lt_succ _⟩ : Fin (obligationCount φ + 1))))

/-- Büchi acceptance is the decidable top-counter test. -/
instance buchiAcceptDecidable (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) : DecidablePred (· ∈ (buchi valuation φ).accept) :=
  fun p => inferInstanceAs (Decidable (p.2.val = obligationCount φ))

end Cslib.LTL.Tableau

namespace Cslib.LTL.ModelChecking

open Automata.NA Automata.ωAcceptor

variable {State Action Atom Q : Type*}

/-- A finite action alphabet makes existential model steps decidable. -/
instance productTrDecidable (lts : LTS State Action) (initial : Set State)
    (a : Buchi Q State) [DecidableEq State] [Fintype Action]
    [∀ s action t, Decidable (lts.Tr s action t)]
    [∀ s x t, Decidable (a.Tr s x t)] (p : State × Q) (x : State) (q : State × Q) :
    Decidable ((product lts initial a).Tr p x q) :=
  inferInstanceAs (Decidable
    (x = p.1 ∧ (∃ action, lts.Tr p.1 action q.1) ∧ a.Tr p.2 x q.2))

/-- Initial states are tested componentwise with the supplied decisions. -/
instance productStartDecidable (lts : LTS State Action) (initial : Set State)
    (a : Buchi Q State) [DecidablePred (· ∈ initial)]
    [DecidablePred (· ∈ a.start)] : DecidablePred (· ∈ (product lts initial a).start) :=
  fun p => inferInstanceAs (Decidable (p.1 ∈ initial ∧ p.2 ∈ a.start))

/-- Product acceptance uses the recognizer's supplied acceptance decision. -/
instance productAcceptDecidable (lts : LTS State Action) (initial : Set State)
    (a : Buchi Q State) [DecidablePred (· ∈ a.accept)] :
    DecidablePred (· ∈ (product lts initial a).accept) :=
  fun p => inferInstanceAs (Decidable (p.2 ∈ a.accept))

section Decidable

variable [Fintype State] [DecidableEq State] [Fintype Action]
  (lts : LTS State Action) [∀ s action t, Decidable (lts.Tr s action t)]
  (initial : Set State) [DecidablePred (· ∈ initial)]
  (valuation : State → Atom → Prop) [∀ s a, Decidable (valuation s a)]
  (φ : Formula Atom)

/-- Full-LTL checking by the existing finite Büchi reachability algorithm.
The finite/decidable data requirements are only for execution, not recognition. -/
def checkB : Bool := by
  letI : DecidablePred (· ∈ (Tableau.buchi valuation (.not φ)).start) :=
    Tableau.buchiStartDecidable valuation (.not φ)
  letI : DecidablePred (· ∈ (Tableau.buchi valuation (.not φ)).accept) :=
    Tableau.buchiAcceptDecidable valuation (.not φ)
  exact (product lts initial (Tableau.buchi valuation (.not φ))).isEmptyB

/-- The executable checker is correct for all initial infinite model runs. -/
theorem checkB_iff :
    checkB lts initial valuation φ = true ↔ Models lts initial valuation φ := by
  let : DecidablePred (· ∈ (Tableau.buchi valuation (.not φ)).start) :=
    Tableau.buchiStartDecidable valuation (.not φ)
  let : DecidablePred (· ∈ (Tableau.buchi valuation (.not φ)).accept) :=
    Tableau.buchiAcceptDecidable valuation (.not φ)
  rw [checkB, Buchi.isEmptyB_iff]
  exact (models_iff_language_empty lts initial valuation φ).symm

end Decidable

end Cslib.LTL.ModelChecking
