/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Tableau

/-!
# Büchi recognition of every LTL formula

Local truth annotations plus one fairness condition per until occurrence
recognize the existing omega-word semantics, including arbitrary negation
and temporal nesting. No finiteness or decidability assumption is placed on
atoms, the input alphabet, or the valuation.

The finite-state construction follows the truth-annotation tableau argument
of Vardi and Wolper, LICS 1986. Degeneralization reuses `GenBuchi.toBuchi`.
Classical logic is used in correctness proofs and in the semantic annotation
witness, not as a future oracle in the automaton's transitions.
-/

@[expose] public section

namespace Cslib.LTL.Tableau

open Filter Automata.ωAcceptor

variable {Atom Symbol : Type*}

private theorem until_witness_of_cutoff (A B U : ℕ → Prop)
    (expand : ∀ n, U n ↔ B n ∨ (A n ∧ U (n + 1))) (d n : ℕ)
    (hU : U n) (halt : ¬ U (n + d) ∨ B (n + d)) :
    ∃ k, B (n + k) ∧ ∀ j < k, A (n + j) := by
  classical
  induction d generalizing n with
  | zero =>
      simp only [Nat.add_zero] at halt
      exact ⟨0, by simpa using halt.resolve_left (not_not.mpr hU),
        fun j hj => by omega⟩
  | succ d ih =>
      rcases (expand n).mp hU with hb | ⟨ha, hu⟩
      · exact ⟨0, by simpa using hb, fun j hj => by omega⟩
      · obtain ⟨k, hb, hp⟩ := ih (n + 1) hu (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using halt)
        refine ⟨k + 1, ?_, fun j hj => ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
        · cases j with
          | zero => simpa using ha
          | succ j =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hp j (by omega)

private theorem until_of_witness (A B U : ℕ → Prop)
    (expand : ∀ n, U n ↔ B n ∨ (A n ∧ U (n + 1))) (k n : ℕ)
    (hb : B (n + k)) (hp : ∀ j < k, A (n + j)) : U n := by
  induction k generalizing n with
  | zero => exact (expand n).mpr (.inl (by simpa using hb))
  | succ k ih =>
      apply (expand n).mpr
      refine .inr ⟨by simpa using hp 0 (by omega), ?_⟩
      apply ih (n + 1)
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hp (j + 1) (by omega)

private theorem until_iff_of_fair_recurrence (A B U : ℕ → Prop)
    (expand : ∀ n, U n ↔ B n ∨ (A n ∧ U (n + 1)))
    (fair : ∃ᶠ n in atTop, ¬ U n ∨ B n) (n : ℕ) :
    U n ↔ ∃ k, B (n + k) ∧ ∀ j < k, A (n + j) := by
  constructor
  · intro hU
    obtain ⟨m, hm, hcut⟩ := frequently_atTop.mp fair n
    apply until_witness_of_cutoff A B U expand (m - n) n hU
    simpa only [Nat.add_sub_cancel' hm] using hcut
  · rintro ⟨k, hb, hp⟩
    exact until_of_witness A B U expand k n hb hp

private theorem until_truth (valuation : Symbol → Atom → Prop)
    (φ ψ : Formula Atom) (w : ωSequence Symbol)
    (ss : ωSequence (State (.until φ ψ)))
    (hstep : ∀ n, step valuation (.until φ ψ) (ss n) (w n) (ss (n + 1)))
    (hfair : Fair (.until φ ψ) ss)
    (hφ : ∀ n, value φ (ss n).2.1 = true ↔ Word.SatisfiesAt valuation w n φ)
    (hψ : ∀ n, value ψ (ss n).2.2 = true ↔ Word.SatisfiesAt valuation w n ψ)
    (n : ℕ) :
    value (.until φ ψ) (ss n) = true ↔ Word.SatisfiesAt valuation w n (.until φ ψ) := by
  have he := until_iff_of_fair_recurrence
    (fun n => value φ (ss n).2.1 = true)
    (fun n => value ψ (ss n).2.2 = true) (fun n => (ss n).1 = true)
    (fun n => (hstep n).1)
    (by simpa only [Bool.eq_false_iff] using hfair.1) n
  refine he.trans ?_
  calc
    _ ↔ ∃ k, Word.SatisfiesAt valuation w (n + k) ψ ∧
        ∀ j < k, Word.SatisfiesAt valuation w (n + j) φ :=
      exists_congr fun k => and_congr (hψ (n + k))
        (forall_congr' fun j => forall_congr' fun _ => hφ (n + j))
    _ ↔ Word.SatisfiesAt valuation w n (.until φ ψ) := by
      change _ ↔ Word.Satisfies valuation (w.drop n) (.until φ ψ)
      rw [Word.Satisfies.until_iff]
      simp only [Word.satisfiesAt_drop]

private theorem truth (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) (w : ωSequence Symbol) (ss : ωSequence (State φ))
    (hstep : ∀ n, step valuation φ (ss n) (w n) (ss (n + 1)))
    (hfair : Fair φ ss) (n : ℕ) :
    value φ (ss n) = true ↔ Word.SatisfiesAt valuation w n φ := by
  induction φ generalizing n with
  | atom a => exact (hstep n).trans Word.satisfiesAt_atom.symm
  | top => exact iff_true_intro (hstep n)
  | not φ ih =>
      exact (hstep n).1.trans (not_congr
        (ih (fun k => (ss k).2) (fun k => (hstep k).2) hfair n))
  | and φ ψ ihφ ihψ =>
      exact (hstep n).1.trans (and_congr
        (ihφ (fun k => (ss k).2.1) (fun k => (hstep k).2.1) hfair.1 n)
        (ihψ (fun k => (ss k).2.2) (fun k => (hstep k).2.2) hfair.2 n))
  | next φ ih =>
      exact (hstep n).1.trans
        ((ih (fun k => (ss k).2) (fun k => (hstep k).2) hfair (n + 1)).trans
          Word.satisfiesAt_next.symm)
  | «until» φ ψ ihφ ihψ =>
      exact until_truth valuation φ ψ w ss hstep hfair
        (fun k => ihφ (fun j => (ss j).2.1) (fun j => (hstep j).2.1) hfair.2.1 k)
        (fun k => ihψ (fun j => (ss j).2.2) (fun j => (hstep j).2.2) hfair.2.2 k) n

open Classical in
private noncomputable def semanticState (valuation : Symbol → Atom → Prop)
    (w : ωSequence Symbol) (n : ℕ) : (φ : Formula Atom) → State φ
  | .atom a => decide (Word.SatisfiesAt valuation w n (.atom a))
  | .top => decide (Word.SatisfiesAt valuation w n .top)
  | .not φ =>
      (decide (Word.SatisfiesAt valuation w n (.not φ)),
        semanticState valuation w n φ)
  | .and φ ψ =>
      (decide (Word.SatisfiesAt valuation w n (.and φ ψ)),
        semanticState valuation w n φ, semanticState valuation w n ψ)
  | .next φ =>
      (decide (Word.SatisfiesAt valuation w n (.next φ)),
        semanticState valuation w n φ)
  | .until φ ψ =>
      (decide (Word.SatisfiesAt valuation w n (.until φ ψ)),
        semanticState valuation w n φ, semanticState valuation w n ψ)

private theorem semantic_value (valuation : Symbol → Atom → Prop)
    (w : ωSequence Symbol) (n : ℕ) (φ : Formula Atom) :
    value φ (semanticState valuation w n φ) = true ↔
      Word.SatisfiesAt valuation w n φ := by
  cases φ <;> simp [semanticState, value]

private theorem satisfiesAt_until_expansion
    (valuation : Symbol → Atom → Prop) (w : ωSequence Symbol)
    (n : ℕ) (φ ψ : Formula Atom) :
    Word.SatisfiesAt valuation w n (.until φ ψ) ↔
      Word.SatisfiesAt valuation w n ψ ∨
        (Word.SatisfiesAt valuation w n φ ∧
          Word.SatisfiesAt valuation w (n + 1) (.until φ ψ)) := by
  simpa only [Word.Satisfies.next_iff, Word.SatisfiesAt,
    ωSequence.drop_drop] using
    (Word.Satisfies.until_expansion (valuation := valuation)
      (w := w.drop n) (φ := φ) (ψ := ψ))

private theorem semantic_until_expansion
    (valuation : Symbol → Atom → Prop) (w : ωSequence Symbol)
    (n : ℕ) (φ ψ : Formula Atom) :
    value (.until φ ψ) (semanticState valuation w n (.until φ ψ)) = true ↔
      value ψ (semanticState valuation w n ψ) = true ∨
        (value φ (semanticState valuation w n φ) = true ∧
          value (.until φ ψ) (semanticState valuation w (n + 1) (.until φ ψ)) = true) :=
  (semantic_value valuation w n (.until φ ψ)).trans
    ((satisfiesAt_until_expansion valuation w n φ ψ).trans
      (or_congr (semantic_value valuation w n ψ).symm
        (and_congr (semantic_value valuation w n φ).symm
          (semantic_value valuation w (n + 1) (.until φ ψ)).symm)))

private theorem semantic_step (valuation : Symbol → Atom → Prop)
    (w : ωSequence Symbol) (φ : Formula Atom) (n : ℕ) :
    step valuation φ (semanticState valuation w n φ) (w n)
      (semanticState valuation w (n + 1) φ) := by
  induction φ generalizing n with
  | atom a => exact (semantic_value valuation w n (.atom a)).trans Word.satisfiesAt_atom
  | top => exact (semantic_value valuation w n .top).mpr trivial
  | not φ ih =>
      refine ⟨?_, ih n⟩
      exact (semantic_value valuation w n (.not φ)).trans
        (not_congr (semantic_value valuation w n φ).symm)
  | and φ ψ ihφ ihψ =>
      refine ⟨?_, ihφ n, ihψ n⟩
      exact (semantic_value valuation w n (.and φ ψ)).trans
        (and_congr (semantic_value valuation w n φ).symm
          (semantic_value valuation w n ψ).symm)
  | next φ ih =>
      refine ⟨?_, ih n⟩
      exact (semantic_value valuation w n (.next φ)).trans
        (Word.satisfiesAt_next.trans (semantic_value valuation w (n + 1) φ).symm)
  | «until» φ ψ ihφ ihψ =>
      exact ⟨semantic_until_expansion valuation w n φ ψ, ihφ n, ihψ n⟩

private theorem semantic_until_fair (valuation : Symbol → Atom → Prop)
    (w : ωSequence Symbol) (φ ψ : Formula Atom) :
    ∃ᶠ n in atTop,
      value (.until φ ψ) (semanticState valuation w n (.until φ ψ)) = false ∨
        value ψ (semanticState valuation w n ψ) = true := by
  rw [frequently_atTop]
  intro N
  by_cases h : Word.SatisfiesAt valuation w N (.until φ ψ)
  · obtain ⟨k, hk, _⟩ := Word.Satisfies.until_iff.mp h
    refine ⟨N + k, by omega, .inr ?_⟩
    exact (semantic_value valuation w (N + k) ψ).mpr
      (Word.satisfiesAt_drop.mp hk)
  · refine ⟨N, le_refl N, .inl ?_⟩
    exact Bool.eq_false_iff.mpr fun hb => h ((semantic_value valuation w N _).mp hb)

private theorem semantic_fair (valuation : Symbol → Atom → Prop)
    (w : ωSequence Symbol) (φ : Formula Atom) :
    Fair φ (fun n => semanticState valuation w n φ) := by
  induction φ with
  | atom a => trivial
  | top => trivial
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | next φ ih => exact ih
  | «until» φ ψ ihφ ihψ =>
      exact ⟨semantic_until_fair valuation w φ ψ, ihφ, ihψ⟩

/-- The full tableau recognizes exactly the existing LTL satisfaction relation. -/
theorem mem_automaton_iff (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) (w : ωSequence Symbol) :
    w ∈ language (automaton valuation φ) ↔ Word.Satisfies valuation w φ := by
  rw [mem_language_iff]
  constructor
  · rintro ⟨ss, hstart, hstep, hfair⟩
    exact (truth valuation φ w ss hstep hfair 0).mp hstart
  · intro h
    refine ⟨fun n => semanticState valuation w n φ,
      (semantic_value valuation w 0 φ).mpr h, ?_, semantic_fair valuation w φ⟩
    exact fun n => semantic_step valuation w φ n

/-- Exact omega-language equality for the generalized tableau. -/
theorem language_automaton (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    language (automaton valuation φ) = Word.language valuation φ :=
  ωLanguage.mem_ext fun w => mem_automaton_iff valuation φ w

/-- Ordinary Büchi recognition, using the existing fairness counter. -/
def buchi (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    Automata.NA.Buchi (State φ × Fin (obligationCount φ + 1)) Symbol :=
  (automaton valuation φ).toBuchi

/-- Every LTL formula has precisely its existing language as a Büchi language. -/
theorem language_buchi (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    language (buchi valuation φ) = Word.language valuation φ :=
  (Automata.NA.GenBuchi.language_toBuchi (automaton valuation φ)).trans
    (language_automaton valuation φ)

/-- The ordinary Büchi recognizer accepts exactly satisfaction of the formula. -/
theorem mem_buchi_iff (valuation : Symbol → Atom → Prop)
    (φ : Formula Atom) (w : ωSequence Symbol) :
    w ∈ language (buchi valuation φ) ↔ Word.Satisfies valuation w φ := by
  rw [language_buchi, Word.mem_language]

end Cslib.LTL.Tableau

namespace Cslib.LTL

open Automata.ωAcceptor

variable {Atom Symbol : Type*}

/-- Every existing LTL formula has a finite-state Büchi recognizer under the
same valuation. Neither atoms nor the alphabet need be finite or decidable. -/
theorem exists_buchi (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S Symbol),
      language a = Word.language valuation φ :=
  ⟨Tableau.State φ × Fin (Tableau.obligationCount φ + 1), inferInstance,
    Tableau.buchi valuation φ, Tableau.language_buchi valuation φ⟩

end Cslib.LTL
