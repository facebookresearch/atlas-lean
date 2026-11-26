/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.SelfStabilization

/-!
# Tests for the self-stabilization criterion

The Boolean examples separate closure, coverage, and convergence. In particular, a scheduler
can admit a convergent run while leaving an initial state with no admitted execution.
-/

namespace Cslib.LTS.SelfStabilizationTests

private def legit (s : Bool) : Prop := s = true

-- A true label sets the state to true; a false label leaves it unchanged.
private def reset : LTS Bool Bool where
  Tr s a t := t = (s || a)

private def admitsReset (_ : ωSequence Bool) (labels : ωSequence Bool) : Prop :=
  ∃ i, labels i = true

private theorem resetClosed : reset.TrInv legit := by
  intro s a t hstep hs
  change s = true at hs
  change t = (s || a) at hstep
  simpa [legit, hs] using hstep

private def resetStates (s : Bool) : ωSequence Bool := ωSequence.cons s (.const true)

private theorem resetExecution (s : Bool) :
    reset.OmegaExecution (resetStates s) (.const true) := by
  intro i
  change true = (resetStates s i || true)
  simp

private theorem resetCoverage (s : Bool) : ∃ ss labels,
    ss 0 = s ∧ reset.OmegaExecution ss labels ∧ admitsReset ss labels :=
  ⟨resetStates s, .const true, rfl, resetExecution s, ⟨0, rfl⟩⟩

private theorem resetStabilizes : reset.SelfStabilizing legit admitsReset := by
  refine ⟨resetClosed, resetCoverage, ?_⟩
  intro ss labels hrun hadm
  obtain ⟨i, hi⟩ := hadm
  have hstep : ss (i + 1) = (ss i || labels i) := hrun i
  exact ⟨i + 1, by simpa [legit, hi] using hstep⟩

-- Apply the equivalence to the admitted execution that starts outside legitimacy.
example : ¬ legit (resetStates false 0) ∧
    ∃ n, ∀ m ≥ n, legit (resetStates false m) := by
  refine ⟨Bool.false_ne_true, ?_⟩
  exact ((selfStabilizing_iff_eventually_always resetClosed).mp resetStabilizes).2
    (resetStates false) (.const true) (resetExecution false) ⟨0, rfl⟩

-- Admitting all runs preserves closure and coverage, but the all-false run never enters `legit`.
example : ¬ reset.SelfStabilizing legit (fun _ _ ↦ True) := by
  intro h
  obtain ⟨n, hn⟩ := h.2.2 (.const false) (.const false) (fun _ ↦ rfl) trivial
  exact Bool.false_ne_true hn

-- Overwriting the state with the label permits a step out of legitimacy.
private def overwrite : LTS Bool Bool where
  Tr _ a t := t = a

private def admitsTrueOnly (_ : ωSequence Bool) (labels : ωSequence Bool) : Prop :=
  ∀ i, labels i = true

-- Coverage and convergence both hold, but closure fails on a step the scheduler disallows.
example : (∀ s, ∃ ss labels, ss 0 = s ∧ overwrite.OmegaExecution ss labels ∧
    admitsTrueOnly ss labels) ∧
    (∀ ss labels, overwrite.OmegaExecution ss labels → admitsTrueOnly ss labels →
      ∃ n, legit (ss n)) ∧ ¬ overwrite.SelfStabilizing legit admitsTrueOnly := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact ⟨resetStates s, .const true, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · intro ss labels hrun hadm
    have hstep : ss 1 = labels 0 := hrun 0
    exact ⟨1, hstep.trans (hadm 0)⟩
  · intro h
    exact Bool.false_ne_true (h.1 true false false rfl rfl)

-- `true` loops and `false` has no outgoing transition.
private def deadlock : LTS Bool Unit where
  Tr s _ t := s = true ∧ t = true

-- All runs are admitted. Closure and convergence hold, with a live legitimate run from `true`,
-- but the old two-clause criterion misses the deadlocked initial state `false`.
example : deadlock.TrInv legit ∧
    (∀ ss labels, deadlock.OmegaExecution ss labels → ∃ n, legit (ss n)) ∧
    (∃ ss labels, ss 0 = true ∧ deadlock.OmegaExecution ss labels) ∧
    ¬ deadlock.SelfStabilizing legit (fun _ _ ↦ True) := by
  refine ⟨fun _ _ _ hstep _ ↦ hstep.2, ?_, ?_, ?_⟩
  · intro ss labels hrun
    exact ⟨0, (hrun 0).1⟩
  · exact ⟨.const true, .const (), rfl, fun _ ↦ ⟨rfl, rfl⟩⟩
  · intro h
    obtain ⟨ss, labels, hstart, hrun, _⟩ := h.2.1 false
    exact Bool.false_ne_true (hstart.symm.trans (hrun 0).1)

end Cslib.LTS.SelfStabilizationTests
