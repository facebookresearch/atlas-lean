/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.LTS.Fairness

namespace Cslib.LTS.FairnessTests

-- Both labels toggle the Boolean state: `none` is always available, while `some b`
-- is available only from state `b`.
private def toggle : LTS Bool (Option Bool) :=
  ⟨fun s label t ↦ t = !s ∧ match label with
    | none => True
    | some b => s = b⟩

private def states : ωSequence Bool := ⟨fun n ↦ decide (n % 2 = 1)⟩

private theorem states_succ (n : ℕ) : states (n + 1) = !(states n) := by
  change decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1)
  by_cases h : n % 2 = 1
  · simp [h, show (n + 1) % 2 ≠ 1 by omega]
  · simp [h, show (n + 1) % 2 = 1 by omega]

private theorem states_even (n : ℕ) : states (2 * n) = false := by
  change decide (2 * n % 2 = 1) = false
  simp

private theorem states_odd (n : ℕ) : states (2 * n + 1) = true := by
  change decide ((2 * n + 1) % 2 = 1) = true
  simp [show (2 * n + 1) % 2 = 1 by omega]

private theorem ignoringExecution : toggle.OmegaExecution states (ωSequence.const none) :=
  fun n ↦ ⟨states_succ n, trivial⟩

private theorem choosingExecution : toggle.OmegaExecution states (states.map some) :=
  fun n ↦ ⟨states_succ n, rfl⟩

private def onlyFalse : Set (Option Bool) := {some false}

private theorem onlyFalse_enabled_iff (s : Bool) :
    toggle.ActionClassEnabled onlyFalse s ↔ s = false := by
  constructor
  · rintro ⟨label, hlabel, t, hstep⟩
    change label = some false at hlabel
    subst label
    exact hstep.2
  · intro hs
    exact ⟨some false, rfl, !s, rfl, hs⟩

-- The class is enabled at every even index, disabled at every odd index, and never taken.
example : ignoringExecution.WeaklyFair onlyFalse ∧ ¬ ignoringExecution.StronglyFair onlyFalse := by
  constructor
  · rintro ⟨start, henabled⟩
    have h := (onlyFalse_enabled_iff _).mp (henabled (2 * start + 1) (by omega))
    rw [states_odd] at h
    contradiction
  · intro h
    have henabled (cutoff : ℕ) : ∃ n ≥ cutoff, toggle.ActionClassEnabled onlyFalse (states n) :=
      ⟨2 * cutoff, by omega, (onlyFalse_enabled_iff _).mpr (states_even cutoff)⟩
    obtain ⟨n, _, hoccurs⟩ := h henabled 0
    change (none : Option Bool) = some false at hoccurs
    cases hoccurs

private def both : Set (Option Bool) := Set.range some

-- The class is always enabled, but neither class label is enabled throughout any tail.
private theorem both_enabled (s : Bool) : toggle.ActionClassEnabled both s :=
  ⟨some s, ⟨s, rfl⟩, !s, rfl, rfl⟩

example (b : Bool) (cutoff : ℕ) : ∃ n ≥ cutoff, ¬ ∃ t, toggle.Tr (states n) (some b) t := by
  cases b
  · refine ⟨2 * cutoff + 1, by omega, ?_⟩
    rintro ⟨t, _, h⟩
    rw [states_odd] at h
    contradiction
  · refine ⟨2 * cutoff, by omega, ?_⟩
    rintro ⟨t, _, h⟩
    rw [states_even] at h
    contradiction

-- The same state sequence is not even weakly fair when it takes only `none`,
-- but is strongly fair when it takes the enabled class label at every step.
example : ¬ ignoringExecution.WeaklyFair both := by
  intro h
  obtain ⟨n, _, b, hoccurs⟩ := h ⟨0, fun i _ ↦ both_enabled (states i)⟩ 0
  change some b = (none : Option Bool) at hoccurs
  cases hoccurs

example : choosingExecution.StronglyFair both := by
  intro _ cutoff
  exact ⟨cutoff, le_rfl, states cutoff, rfl⟩

-- The same label marks both the self-loop at `false` and the exit to `true`.
private def stutterOrExitAction (s _t : Bool) : Prop := s = false

private def stutterOrExit : LTS Bool Unit := ⟨fun s _ t ↦ stutterOrExitAction s t⟩

private def stutteringStates : ωSequence Bool := ωSequence.const false

private theorem stutteringExecution : stutterOrExit.OmegaExecution stutteringStates
    (ωSequence.const ()) := fun _ ↦ rfl

example : stutteringExecution.WeaklyFair ({()} : Set Unit) ∧
    stutteringExecution.StronglyFair ({()} : Set Unit) := by
  have h : stutteringExecution.StronglyFair ({()} : Set Unit) :=
    fun _ cutoff ↦ ⟨cutoff, le_rfl, rfl⟩
  exact ⟨h.weaklyFair, h⟩

-- For `f := id`, only the exit is a nonstuttering action step.
private def nonstutteringStep (s t : Bool) : Prop := stutterOrExitAction s t ∧ t ≠ s

-- Always enabled, never taken: neither of Lamport's fairness conditions holds.
example : (∀ n, ∃ t, nonstutteringStep (stutteringStates n) t) ∧
    (∀ n, ¬ nonstutteringStep (stutteringStates n) (stutteringStates (n + 1))) := by
  exact ⟨fun _ ↦ ⟨true, rfl, show true ≠ false by decide⟩, fun _ h ↦ h.2 rfl⟩

end Cslib.LTS.FairnessTests
