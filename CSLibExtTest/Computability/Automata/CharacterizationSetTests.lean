/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.Transducers.CharacterizationSet

@[expose] public section

/-!
# Tests for characterization sets of Mealy machines

* A two-state machine whose states are separated by a one-letter word: `{ε}` is not a
  characterization set, since `ε` separates no states, and `{ε, a}` is one, with words of
  length at most `2 - 1`.
* A three-state machine with two states that agree on every word of length at most `1`: every
  characterization set contains a word of length at least `3 - 1 = 2`, and
  `exists_characterization_set` gives one whose longest word has length exactly `2`.
* A two-state machine whose states are equivalent but distinct, so the machine is not minimal:
  `{ε}` is a characterization set.
* For a one-state machine, the set `exists_characterization_set` gives is `{ε}`.
* Axiom audit for the new API.
-/

set_option autoImplicit false

open Cslib.Automata

namespace Cslib.Automata.MealyMachine.CharacterizationSetTests

/-- A two-state machine over one input letter that stays in its state and outputs it. -/
def echo : MealyMachine Bool Unit Bool where
  step q _ := (q, q)
  start := false

/-- The empty word separates no states: `{ε}` is not a characterization set of `echo`, whose
two states give different outputs on the one-letter word. -/
example : ¬ ∀ q q' : Bool, (∀ w ∈ ({[]} : Finset (List Unit)),
    echo.runOut q w = echo.runOut q' w) → ∀ w, echo.runOut q w = echo.runOut q' w := by
  intro h
  have := h false true (fun w hw => by rw [Finset.mem_singleton.mp hw]; rfl) [()]
  exact absurd this (by decide)

/-- `{ε, a}` is a characterization set of the two-state machine `echo`, and its words have
length at most `2 - 1 = 1`, the bound of `exists_characterization_set`. -/
example : (∀ w ∈ ({[], [()]} : Finset (List Unit)), w.length ≤ Fintype.card Bool - 1) ∧
    ∀ q q' : Bool, (∀ w ∈ ({[], [()]} : Finset (List Unit)),
      echo.runOut q w = echo.runOut q' w) → ∀ w, echo.runOut q w = echo.runOut q' w := by
  refine ⟨by decide, fun q q' h w => ?_⟩
  have hq : [q] = [q'] := h [()] (by simp)
  rw [List.cons.inj hq |>.1]

/-- A three-state machine over one input letter: `0` moves to `1`, and `1` and `2` move to `2`;
the output is `true` exactly in state `2`. -/
def delay : MealyMachine (Fin 3) Unit Bool where
  step q _ := (if q = 0 then 1 else 2, decide (q = 2))
  start := 0

/-- The states `0` and `1` of `delay` agree on every input word of length at most `1` but
differ on the word of length `2`. -/
example : (∀ w : List Unit, w.length ≤ 1 → delay.runOut 0 w = delay.runOut 1 w) ∧
    delay.runOut 0 [(), ()] ≠ delay.runOut 1 [(), ()] := by
  refine ⟨fun w hw => ?_, by decide⟩
  match w, hw with
  | [], _ => rfl
  | [()], _ => rfl

/-- Every characterization set of the three-state machine `delay` contains a word of length at
least `3 - 1 = 2`: the bound of `exists_characterization_set` is attained. -/
example (W : Finset (List Unit)) (hW : ∀ q q' : Fin 3,
    (∀ w ∈ W, delay.runOut q w = delay.runOut q' w) → ∀ w, delay.runOut q w = delay.runOut q' w) :
    ∃ w ∈ W, Fintype.card (Fin 3) - 1 ≤ w.length := by
  by_contra hshort
  simp only [not_exists, not_and, not_le] at hshort
  have hagree : ∀ w ∈ W, delay.runOut 0 w = delay.runOut 1 w := by
    intro w hw
    have hlen : w.length ≤ 1 := by
      have := hshort w hw
      simp only [Fintype.card_fin] at this
      omega
    match w, hlen with
    | [], _ => rfl
    | [()], _ => rfl
  exact absurd (hW 0 1 hagree [(), ()]) (by decide)

/-- Non-vacuity: `exists_characterization_set` gives `delay` a characterization set whose
longest word has length exactly `2`. -/
example : ∃ W : Finset (List Unit), [] ∈ W ∧ (∀ w ∈ W, w.length ≤ 2) ∧ (∃ w ∈ W, w.length = 2) ∧
    ∀ q q' : Fin 3, (∀ w ∈ W, delay.runOut q w = delay.runOut q' w) →
      ∀ w, delay.runOut q w = delay.runOut q' w := by
  obtain ⟨W, hnil, hlen, hW⟩ := delay.exists_characterization_set
  simp only [Fintype.card_fin] at hlen
  refine ⟨W, hnil, hlen, ?_, hW⟩
  have hshort : ¬ ∀ w ∈ W, w.length ≤ 1 := by
    intro hshort
    have hagree : ∀ w ∈ W, delay.runOut 0 w = delay.runOut 1 w := by
      intro w hw
      match w, hshort w hw with
      | [], _ => rfl
      | [()], _ => rfl
    exact absurd (hW 0 1 hagree [(), ()]) (by decide)
  simp only [not_forall, not_le] at hshort
  obtain ⟨w, hw, hw1⟩ := hshort
  exact ⟨w, hw, by have := hlen w hw; omega⟩

/-- A two-state machine with a single output letter: its two states are equivalent but
distinct, so it is not minimal. -/
def toggle : MealyMachine Bool Unit Unit where
  step q _ := (!q, ())
  start := false

/-- Without minimality, `{ε}` can be a characterization set: the two states of `toggle` are
equivalent, so agreement on any set of words implies equivalence. -/
example : ∀ q q' : Bool, (∀ w ∈ ({[]} : Finset (List Unit)),
    toggle.runOut q w = toggle.runOut q' w) → ∀ w, toggle.runOut q w = toggle.runOut q' w := by
  intro q q' _ w
  induction w generalizing q q' with
  | nil => rfl
  | cons a w ih =>
    rw [runOut_cons, runOut_cons, ih (toggle.step q a).1 (toggle.step q' a).1
      (fun v hv => by rw [Finset.mem_singleton.mp hv]; rfl)]

/-- For a machine with one state, the characterization set of `exists_characterization_set`
is `{ε}`: its words have length at most `1 - 1 = 0`. -/
example {In Out : Type*} (M : MealyMachine Unit In Out) :
    ∃ W : Finset (List In), W = {[]} ∧ ∀ q q' : Unit,
      (∀ w ∈ W, M.runOut q w = M.runOut q' w) → ∀ w, M.runOut q w = M.runOut q' w := by
  obtain ⟨W, hnil, hlen, hW⟩ := M.exists_characterization_set
  refine ⟨W, ?_, hW⟩
  ext w
  simp only [Finset.mem_singleton]
  constructor
  · intro hw
    have := hlen w hw
    simp only [Fintype.card_unit, Nat.sub_self, Nat.le_zero, List.length_eq_zero_iff] at this
    exact this
  · rintro rfl
    exact hnil

end Cslib.Automata.MealyMachine.CharacterizationSetTests

#print axioms Cslib.Automata.MealyMachine.exists_characterization_set
