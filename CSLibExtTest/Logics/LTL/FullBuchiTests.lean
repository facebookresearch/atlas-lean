/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.DecidableModelChecking

/-!
# Adversarial consumers of full-LTL recognition and model checking

These tests use infinitely many possible atoms (`Nat`), both truth values,
until fulfillment and infinite postponement, nested temporal operators,
GF versus FG, and concrete finite models including a deadlock.
-/

@[expose] public section

namespace Cslib.LTL.FullBuchiTests

open Filter Automata.ωAcceptor ModelChecking

/-- Atom 0 holds on true, atom 1 on false, and all other atoms are false. -/
def val (x : Bool) (a : ℕ) : Prop :=
  if a = 0 then x = true else if a = 1 then x = false else False

instance : ∀ x a, Decidable (val x a) := fun x a =>
  inferInstanceAs (Decidable (if a = 0 then x = true else if a = 1 then x = false else False))

/-- Constant input words, with no finite-atom assumption. -/
def constant (x : Bool) : ωSequence Bool := ωSequence.const x

example : Fintype.card (Tableau.State (.until (.atom 0) (.atom 1) : Formula ℕ)) = 8 := by
  decide

example : Tableau.obligationCount (Formula.always (Formula.eventually (.atom 0 : Formula ℕ))) = 2 :=
  rfl

/-- Until may finish immediately even when its guard is false. -/
example : constant false ∈ language (Tableau.buchi val (.until (.atom 0) (.atom 1))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.until_iff]
  exact ⟨0, by simp [Word.satisfiesAt_atom, val, constant], fun j hj => by omega⟩

/-- An always-true guard does not permit infinite postponement of the target. -/
example : constant true ∉ language (Tableau.buchi val (.until (.atom 0) (.atom 1))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.until_iff]
  rintro ⟨k, hk, _⟩
  simp [Word.satisfiesAt_atom, val, constant] at hk

/-- A locally consistent but unfair annotation postpones until forever. -/
def postpone : Tableau.State (.until (.atom 0) (.atom 1) : Formula ℕ) :=
  (true, true, false)

example : (Tableau.automaton val (.until (.atom 0) (.atom 1))).Run
    (constant true) (ωSequence.const postpone) := by
  refine ⟨rfl, ?_⟩
  intro n
  change Tableau.step val (.until (.atom 0) (.atom 1))
    (true, true, false) true (true, true, false)
  simp [Tableau.step, Tableau.value, val]

example : ¬ Tableau.Fair (.until (.atom 0) (.atom 1)) (ωSequence.const postpone) := by
  simp [Tableau.Fair, Tableau.value, postpone]

example : Tableau.obligation (.until (.atom 0) (.atom 1)) ⟨0, by decide⟩ postpone = false := by
  decide

/-- False initially, then true forever. -/
def late : ωSequence Bool := fun n => decide (0 < n)

example : late ∈ language (Tableau.buchi val (.next (.atom 0))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.next_iff, Word.satisfiesAt_atom]
  simp [val, late]

example : late ∉ language (Tableau.buchi val (.atom 0)) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.atom_iff]
  simp [val, late]

/-- Next checks the destination body, not the current body or destination root. -/
example : Tableau.step val (.next (.atom 0)) (true, false) false (false, true) := by
  simp [Tableau.step, Tableau.value, val]

/-- Negation preserves the false-until solution rather than guessing truth. -/
example : constant true ∈ language (Tableau.buchi val (.not (.until .top (.atom 1)))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.not_iff, Word.Satisfies.until_iff]
  simp [Word.satisfiesAt_atom, val, constant]

/-- Release permits its right operand to hold forever with no release event. -/
example : constant false ∈ language (Tableau.buchi val (Formula.release (.atom 0) (.atom 1))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.release_iff]
  intro k
  exact .inl (by simp [Word.satisfiesAt_atom, val, constant])

/-- The right operand of release must hold at the release position itself. -/
example : constant true ∉ language (Tableau.buchi val (Formula.release (.atom 0) (.atom 1))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.release_iff]
  intro h
  have h0 := h 0
  simp [Word.satisfiesAt_atom, val, constant] at h0

/-- Two true letters, then false forever. -/
def switching : ωSequence Bool := fun n => decide (n < 2)

/-- A non-propositional body under G, outside the old safety fragment. -/
example : switching ∈ language (Tableau.buchi val
    (Formula.always (Formula.or (.atom 0) (.next (.atom 1))))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.always_iff]
  intro k
  rw [Word.SatisfiesAt, Word.Satisfies.or_iff]
  by_cases hk : k < 2
  · left
    simpa [Word.Satisfies, val, switching] using (show k ≤ 1 by omega)
  · right
    rw [Word.Satisfies.next_iff, Word.satisfiesAt_drop, Word.satisfiesAt_atom]
    simpa [val, switching] using (show k ≠ 0 by omega)

/-- The preceding G of a disjunction cannot be replaced by disjoined Gs. -/
example : switching ∉ language (Tableau.buchi val (Formula.always (.atom 0))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.always_iff]
  intro h
  have h2 := h 2
  simp [Word.satisfiesAt_atom, val, switching] at h2

example : switching ∉ language (Tableau.buchi val (Formula.always (.next (.atom 1)))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.always_iff]
  intro h
  have h0 := h 0
  rw [Word.satisfiesAt_next, Word.satisfiesAt_atom] at h0
  simp [val, switching] at h0

/-- A genuine two-letter periodic input, with true at even positions. -/
def alternating : ωSequence Bool := fun n => decide (n % 2 = 0)

example : alternating ∈ language (Tableau.buchi val
    (Formula.always (Formula.eventually (.atom 0)))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.always_eventually_iff, frequently_atTop]
  intro N
  exact ⟨2 * N, by omega, by simp [Word.satisfiesAt_atom, val, alternating]⟩

example : alternating ∉ language (Tableau.buchi val
    (Formula.eventually (Formula.always (.atom 0)))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.eventually_always_iff, eventually_atTop]
  rintro ⟨N, h⟩
  have hh := h (2 * N + 1) (by omega)
  have hm : (2 * N + 1) % 2 = 1 := by omega
  simp [Word.satisfiesAt_atom, val, alternating, hm] at hh

example : late ∈ language (Tableau.buchi val
    (Formula.eventually (Formula.always (.atom 0)))) := by
  rw [Tableau.mem_buchi_iff, Word.Satisfies.eventually_always_iff, eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  simpa [Word.satisfiesAt_atom, val, late] using (show 0 < k by omega)

/-- Atom-free formulas work even when the atom type is empty. -/
example (valuation : Unit → Empty → Prop) :
    ωSequence.const () ∈ language (Tableau.buchi valuation .top) :=
  (Tableau.mem_buchi_iff valuation .top _).mpr trivial

/-- Neither enumeration nor equality of function-valued atoms is required. -/
example (valuation : Unit → (ℕ → Bool) → Prop) (φ : Formula (ℕ → Bool)) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S Unit),
      language a = Word.language valuation φ := exists_buchi valuation φ

/-- The arbitrary-alphabet recognition result does not assume a nonempty alphabet. -/
example (valuation : Empty → ℕ → Prop) (φ : Formula ℕ) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S Empty),
      language a = Word.language valuation φ := exists_buchi valuation φ

/-- Empty fairness families, missed obligations, hits, and resets all execute. -/
example : Tableau.advance (.top : Formula ℕ) 0 true = 0 := by decide

example : Tableau.advance (.until (.atom 0) (.atom 1)) ⟨0, by decide⟩ postpone = 0 := by
  decide

example : Tableau.advance (.until (.atom 0) (.atom 1)) ⟨0, by decide⟩
    (true, false, true) = 1 := by decide

example : Tableau.advance (.until (.atom 0) (.atom 1)) ⟨1, by decide⟩ postpone = 0 := by
  decide

end Cslib.LTL.FullBuchiTests
