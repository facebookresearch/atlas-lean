/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.HoareCompleteness

/-!
# Tests for soundness and relative completeness of IMP Hoare logic

* `{True} skip {False}` is not derivable.
* A diverging loop has a derivable partial-correctness triple with postcondition
  `False`, obtained from `Derivable.complete`, and no derivable
  total-correctness triple, by `TDerivable.sound`.
* A total-correctness derivation of a countdown loop built from the rules
  directly, with the variant rule.
* `iterationCount` of the countdown loop is the initial counter value.
* The same derivations through the CSLib inference-system interface on
  `Triple`.
-/

@[expose] public section

namespace Cslib.IMP.HoareCompletenessTests

/-- `while true do skip`. -/
def spin : Cmd := .while (.truth true) .skip

theorem spin_diverges {initial final : State} : ¬ BigStep spin initial final := by
  intro h
  obtain ⟨n, hn⟩ := Iterates.exists_of_bigStep (guard := .truth true) (body := .skip) h
  clear h
  induction n generalizing initial with
  | zero =>
      cases hn with
      | exit hguard => simp at hguard
  | succ n ih =>
      cases hn with
      | step _ _ hrest => exact ih hrest

/-- Completeness yields a partial-correctness derivation for the diverging
loop, even with postcondition `False`. -/
theorem spin_derivable : Derivable (fun _ => True) spin (fun _ => False) :=
  Derivable.complete fun _ _ _ hstep => spin_diverges hstep

/-- No total-correctness derivation exists for the diverging loop, whatever
the postcondition. -/
theorem spin_not_tderivable (post : Assertion) :
    ¬ TDerivable (fun _ => True) spin post := by
  intro h
  obtain ⟨final, hstep, _⟩ := h.sound (s := fun _ => 0) trivial
  exact spin_diverges hstep

/-- `Derivable` is not trivial: `{True} skip {False}` is not derivable. -/
example : ¬ Derivable (fun _ => True) .skip (fun _ => False) :=
  fun h => h.sound (initial := fun _ => 0) trivial (.skip _)

/-- The two systems differ: `TDerivable` is strictly stronger. -/
example : ¬ (∀ pre command post, Derivable pre command post →
    TDerivable pre command post) :=
  fun h => spin_not_tderivable _ (h _ _ _ spin_derivable)

def countdownGuard : BExp := .not (.eq (.var 0) (.const 0))

def countdownBody : Cmd := .assign 0 (.sub (.var 0) (.const 1))

/-- `while x0 ≠ 0 do x0 := x0 - 1`. -/
def countdown : Cmd := .while countdownGuard countdownBody

@[simp] theorem countdownGuard_eval (state : State) :
    countdownGuard.eval state = !decide (state 0 = 0) := rfl

/-- A total-correctness derivation of the countdown loop, built from the
rules: variant `x0`, invariant `True`. -/
theorem countdown_tderivable :
    TDerivable (fun _ => True) countdown (fun state => state 0 = 0) := by
  refine .consequence (Assertion.entails_refl _)
    (.whileVariant (invariant := fun _ => True) (variant := fun state => state 0) ?_) ?_
  · intro n
    refine .consequence ?_ (.assign _ 0 _) (Assertion.entails_refl _)
    rintro state ⟨-, hguard, rfl⟩
    have hne : state 0 ≠ 0 := by simpa using hguard
    simp only [Assertion.subst, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
      Function.update_self]
    exact ⟨trivial, by omega⟩
  · rintro state ⟨-, hguard⟩
    simpa using hguard

/-- The derivation is sound: the countdown terminates with `x0 = 0`. -/
example (state : State) : ∃ final, BigStep countdown state final ∧ final 0 = 0 :=
  countdown_tderivable.sound (s := state) trivial

/-- The countdown loop runs exactly `x0` iterations. -/
theorem countdown_iterates (k : Nat) :
    ∀ state : State, state 0 = k → ∃ final, Iterates countdownGuard countdownBody k state final := by
  induction k with
  | zero =>
      intro state hk
      exact ⟨state, .exit (by simp [hk])⟩
  | succ k ih =>
      intro state hk
      obtain ⟨final, hfinal⟩ := ih (Function.update state 0 (state 0 - 1))
        (by simp [hk])
      exact ⟨final, .step (by simp [hk]) (.assign state 0 _) hfinal⟩

theorem countdown_iterationCount (state : State) :
    iterationCount countdownGuard countdownBody state = state 0 := by
  obtain ⟨final, hfinal⟩ := countdown_iterates (state 0) state rfl
  exact hfinal.iterationCount_eq

example : iterationCount countdownGuard countdownBody (fun _ => 3) = 3 :=
  countdown_iterationCount _

/-- `iterationCount` is `0` on a diverging loop. -/
example : iterationCount (.truth true) .skip (fun _ => 0) = 0 :=
  iterationCount_eq_zero fun _ => spin_diverges

/-- The countdown derivation as a derivation in the CSLib total-correctness
inference system on triples. -/
example : Cslib.Logic.InferenceSystem.DerivableIn TotalCorrectness
    (⟨fun _ => True, countdown, fun state => state 0 = 0⟩ : Triple) :=
  ⟨countdown_tderivable⟩

/-- In the default (partial-correctness) inference system, the diverging loop
satisfies any postcondition. -/
example : Cslib.Logic.InferenceSystem.Derivable
    (⟨fun _ => True, spin, fun _ => False⟩ : Triple) :=
  (Triple.derivable_iff_valid _).mpr fun _ _ _ hstep => spin_diverges hstep

end Cslib.IMP.HoareCompletenessTests
