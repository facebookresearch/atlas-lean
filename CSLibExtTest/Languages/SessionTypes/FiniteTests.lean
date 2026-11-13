/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Progress

/-!
# Finite session consumers and countermodels

The echo pair forwards the received name as data. The two-channel cyclic wait
is linearly typed and dual-compatible, but violates the structural progress
hypothesis. No arbitrary π deadlock-freedom is asserted here.
-/

namespace Cslib.SessionTypes.Tests

open PiCalculus

private def only (a : Nat) (s : SessionType) : Context :=
  advance (fun _ => .end) a s

private def client (a d : Nat) : Proc :=
  .out (.const a) (.const d) (.inp (.const a) .nil)

private def echo (a : Nat) : Proc :=
  .inp (.const a) (.out (.const a) (.var 0) .nil)

/-- Both directions of a nonempty finite protocol have the expected dual. -/
theorem alternating_duality :
    (SessionType.send (.recv .end)).dual = .recv (.send .end) := rfl

/-- The sender uses its endpoint exactly once in each protocol state. -/
theorem client_typed (a d : Nat) :
    HasType 0 (only a (.send (.recv .end))) (client a d) := by
  apply HasType.out (s := .recv .end)
  · simp [only, advance]
  · trivial
  · apply HasType.inp (s := .end)
    · simp [advance]
    · apply HasType.nil
      intro c
      by_cases hc : c = a <;> simp [only, advance, hc]

/-- The input-bound name can be forwarded without acquiring a capability. -/
theorem echo_typed (a : Nat) :
    HasType 0 (dualContext (only a (.send (.recv .end)))) (echo a) := by
  apply HasType.inp (s := .send .end)
  · simp [dualContext, only, advance, SessionType.dual]
  · apply HasType.out (s := .end)
    · simp [advance]
    · exact Nat.zero_lt_one
    · apply HasType.nil
      intro c
      by_cases hc : c = a <;>
        simp [dualContext, only, advance, SessionType.dual, hc]

/-- The first communication actually substitutes the received payload. -/
theorem echo_first_step (a d : Nat) :
    CommStep (client a d, echo a)
      (.inp (.const a) .nil, .out (.const a) (.const d) .nil) :=
  .send a (.const d) (.inp (.const a) .nil)
    (.out (.const a) (.var 0) .nil)

/-- The opposite orientation communicates next and completes. -/
theorem echo_second_step (a d : Nat) :
    CommStep (.inp (.const a) .nil, .out (.const a) (.const d) .nil)
      (.nil, .nil) := .recv a (.const d) .nil .nil

/-- The concrete two-step echo path exists in the original π reduction. -/
theorem echo_pi_path (a d : Nat) :
    Relation.ReflTransGen PiCalculus.Step (represent (client a d, echo a))
      (represent (.nil, .nil)) :=
  represent_steps ((Relation.ReflTransGen.single (echo_first_step a d)).trans
    (Relation.ReflTransGen.single (echo_second_step a d)))

/-- The general progress theorem applies to a populated communicating pair. -/
theorem echo_progress (a d : Nat) :
    (client a d, echo a) = (.nil, .nil) ∨
      ∃ t, CommStep (client a d, echo a) t := by
  apply progress (a := a) ⟨client_typed a d, echo_typed a⟩
  intro c hc
  simp [only, advance, hc]

/-- General finite completion, independently of the explicit two-step proof. -/
theorem echo_finite_completion (a d : Nat) :
    Relation.ReflTransGen CommStep (client a d, echo a) (.nil, .nil) := by
  apply finite_completion (.send (.recv .end)) (a := a)
    ⟨client_typed a d, echo_typed a⟩
  · intro c hc
    simp [only, advance, hc]
  · simp [only, advance]

/-- Parallel duplication of a thread has no linear typing derivation. -/
theorem parallel_duplication_rejected (Γ : Context) (p q : Proc) :
    ¬ HasType 0 Γ (.par p q) := by
  intro h
  cases h

/-- `nil` cannot discard an outstanding send obligation. -/
theorem unfinished_nil_rejected (a : Nat) :
    ¬ HasType 0 (only a (.send .end)) .nil := by
  intro h
  cases h with
  | nil hΓ => simpa [only, advance] using hΓ a

/-- A top-level payload cannot refer to a nonexistent input binder. -/
theorem unbound_payload_rejected (a : Nat) :
    ¬ HasType 0 (only a (.send .end)) (.out (.const a) (.var 0) .nil) := by
  intro h
  cases h with
  | out _ hb => exact Nat.not_lt_zero 0 hb

/-- Completed protocols type inert threads and have a zero-step path. -/
theorem inert_completion :
    Relation.ReflTransGen CommStep (.nil, .nil) (.nil, .nil) :=
  finite_completion .end (a := 0)
    (Γ := fun _ => .end) ⟨.nil (fun _ => rfl), .nil (fun _ => rfl)⟩
    (fun _ _ => rfl) rfl

/-- A received payload is not a session subject: delegation is out of scope. -/
theorem payload_subject_rejected (Γ : Context) :
    ¬ HasType 1 Γ (.out (.var 0) (.const 0) .nil) := by
  intro h
  cases h

/-- Two sends on the same channel cannot have pointwise dual typing. -/
theorem same_direction_rejected (a d : Nat) :
    ¬ BinaryTyped (only a (.send .end))
      (.out (.const a) (.const d) .nil, .out (.const a) (.const d) .nil) := by
  intro h
  cases h.2 with
  | out ha => simp [dualContext, only, advance, SessionType.dual] at ha

/-- A nonzero cutoff under an input lifts the substituted bound name,
so it keeps referring to the outer input, not the new innermost one. -/
theorem nested_substitution :
    PiCalculus.substProc (.var 0) 1
      (.inp (.const 0) (.out (.const 0) (.var 2) .nil)) =
      .inp (.const 0) (.out (.const 0) (.var 1) .nil) := rfl

/-- The same nested bound-name substitution satisfies the typing theorem. -/
theorem nested_substitution_typed :
    HasType 1 (only 0 (.recv (.send .end)))
      (.inp (.const 0) (.out (.const 0) (.var 1) .nil)) := by
  have h : HasType 2 (only 0 (.recv (.send .end)))
      (.inp (.const 0) (.out (.const 0) (.var 2) .nil)) := by
    apply HasType.inp (s := .send .end)
    · simp [only, advance]
    · apply HasType.out (s := .end)
      · simp [advance]
      · exact Nat.lt_succ_self 2
      · apply HasType.nil
        intro c
        by_cases hc : c = 0 <;> simp [only, advance, hc]
  exact h.substProc (b := .var 0) (k := 1) (Nat.zero_lt_one) (Nat.le_refl 1)

/-- Removing the cutoff bound from scoping preservation would be false. -/
theorem invalid_cutoff_counterexample :
    ¬ (substName (.const 7) 1 (.var 0)).ClosedAt 0 := by
  simp [Name.ClosedAt, substName]

/-- The typed echo representation satisfies the shared π scoping judgement. -/
theorem echo_pair_closed (a d : Nat) :
    (represent (client a d, echo a)).ClosedAt 0 :=
  ⟨(client_typed a d).closedAt, (echo_typed a).closedAt⟩

/-- Inserting the locally closed pair under a binder captures no variables. -/
theorem lift_echo_pair_fixed (a d : Nat) :
    liftProc 0 (represent (client a d, echo a)) =
      represent (client a d, echo a) :=
  liftProc_eq_of_closedAt (echo_pair_closed a d)

end Cslib.SessionTypes.Tests
