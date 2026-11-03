/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Progress
import CSLibExt.Languages.PiCalculus.Behavioural

/-!
# Cyclic wait is not excluded by local linear session typing

Two dual-compatible threads wait on different channels before sending on the
other channel. Both sessions are finite. This refutes progress from dual typing
alone. The canonical π unguarded-output invariant proves there is no
`PiCalculus.Step`, including reduction modulo arbitrary structural congruence.
-/

namespace Cslib.SessionTypes.CyclicTests

open PiCalculus

/-- Receive on channel zero, then send on channel one. -/
def leftThread : Proc :=
  .inp (.const 0) (.out (.const 1) (.const 2) .nil)

/-- The opposite endpoint roles, but with the incompatible waiting order. -/
def rightThread : Proc :=
  .inp (.const 1) (.out (.const 0) (.const 2) .nil)

/-- Each channel is owned linearly, with one action on each. -/
def cyclicContext : Context := fun c =>
  if c = 0 then .recv .end else if c = 1 then .send .end else .end

/-- The waiting left thread satisfies its entire linear context. -/
theorem left_typed : HasType 0 cyclicContext leftThread := by
  apply HasType.inp (s := .end)
  · simp [cyclicContext]
  · apply HasType.out (s := .end)
    · simp [advance, cyclicContext]
    · trivial
    · apply HasType.nil
      intro c
      by_cases hc0 : c = 0 <;> by_cases hc1 : c = 1 <;>
        simp [advance, cyclicContext, hc0, hc1]

/-- The waiting right thread satisfies the pointwise dual context. -/
theorem right_typed : HasType 0 (dualContext cyclicContext) rightThread := by
  apply HasType.inp (s := .end)
  · simp [dualContext, cyclicContext, SessionType.dual]
  · apply HasType.out (s := .end)
    · simp [advance, dualContext, cyclicContext, SessionType.dual]
    · trivial
    · apply HasType.nil
      intro c
      by_cases hc0 : c = 0 <;> by_cases hc1 : c = 1 <;>
        simp [advance, dualContext, cyclicContext, SessionType.dual, hc0, hc1]

/-- Dual compatibility alone permits this cyclic waiting configuration. -/
theorem cyclic_typed :
    BinaryTyped cyclicContext (leftThread, rightThread) :=
  ⟨left_typed, right_typed⟩

/-- Neither input guard has an output partner in the other thread's head. -/
theorem cyclic_no_communication (t : Proc × Proc) :
    ¬ CommStep (leftThread, rightThread) t := by
  intro h
  cases h

/-- No choice of designated channel makes this a single-channel network. -/
theorem cyclic_not_single (a : Nat) : ¬ SingleChannel cyclicContext a := by
  intro h
  have h0 : 0 = a := h.active_eq (by simp [cyclicContext])
  have h1 : 1 = a := h.active_eq (by simp [cyclicContext])
  omega

/-- The dual-typed cyclic pair is neither completed nor communicable. -/
theorem dual_typing_not_progress :
    ¬ ((leftThread, rightThread) = (.nil, .nil) ∨
      ∃ t, CommStep (leftThread, rightThread) t) := by
  rintro (h | ⟨t, ht⟩)
  · cases h
  · exact cyclic_no_communication t ht

/-- This cyclic wait cannot reduce even modulo arbitrary π structural
congruence, by the π lane's canonical unguarded-output invariant. -/
theorem cyclic_no_pi_step (q : Proc) :
    ¬ PiCalculus.Step (represent (leftThread, rightThread)) q := by
  apply not_step_of_no_output
  simp [represent, leftThread, rightThread, HasUnguardedOutput]

/-- Balanced local typing does not imply progress in the π semantics. -/
theorem dual_typing_not_pi_progress :
    ¬ ((leftThread, rightThread) = (.nil, .nil) ∨
      ∃ q, PiCalculus.Step (represent (leftThread, rightThread)) q) := by
  rintro (h | ⟨q, hq⟩)
  · cases h
  · exact cyclic_no_pi_step q hq

end Cslib.SessionTypes.CyclicTests
