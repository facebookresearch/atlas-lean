/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress

/-!
# GENERAL qualified runtime progress: idle and missing-service boundaries
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeProgressTests

open PiCalculus Endpoint.Runtime

private def waiting : Proc := .par senderDaemon receiverDaemon
private def missing : Proc := .par (senderRequest (.var 0)) (receiverRequest (.var 0))

private theorem waiting_typed (r : Role) : Runtime.HasType 0 (services r) ∅ waiting := by
  simpa only [waiting, Finmap.union_empty] using
    Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context))
    (sender_daemon_typed 0 r) (receiver_daemon_typed 0 r)

private theorem waiting_idle (r : Role) : Idle (services r) waiting :=
  ⟨⟨710, rfl, Finmap.mem_of_lookup_eq_some (sender_declared r)⟩,
    ⟨711, rfl, Finmap.mem_of_lookup_eq_some (receiver_declared r)⟩⟩

private theorem waiting_available (r : Role) : Available (services r) waiting := by
  intro s sig hs
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hs) with he | he
  · subst s
    exact Or.inr rfl
  · have heq := (Finmap.mem_singleton _ _ _).mp he
    subst s
    exact Or.inl rfl

/-- GENERAL progress chooses Idle for genuine offered waiting services: they are
NOT Cong nil and have no canonical Step, despite exact empty linear ownership. -/
theorem general_waiting_idle (r : Role) : Idle (services r) waiting ∧
    (∀ q, ¬ PiCalculus.Step waiting q) ∧ ¬ Cong waiting .nil ∧ Available (services r) waiting := by
  have hi : Idle (services r) waiting := by
    rcases (waiting_typed r).progress_empty (waiting_available r) with hi | ⟨q, hs⟩
    · exact hi
    · exact False.elim ((waiting_idle r).no_step q hs)
  refine ⟨hi, hi.no_step, ?_, waiting_available r⟩
  intro hc
  have hinput := (input_cong hc).mp (show HasUnguardedInput waiting from Or.inl trivial)
  exact hinput

private theorem missing_typed (r : Role) : Runtime.HasType 1 (services r)
    (recurringInterface (.var 0) r) missing := by
  apply Runtime.HasType.par
  · cases r <;> simp [Finmap.Disjoint, Finmap.mem_singleton, Role.opposite]
  · exact sender_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h)
  · exact receiver_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h)

/-- All OTHER GLOBAL premises are satisfiable, but missing persistent services
make EXISTING Available false. The real typed balanced requests are stuck/notIdle;
this refutes deleting the qualifier, not the correctly qualified theorem. -/
theorem missing_falsifies_qualification (r : Role) :
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) missing ∧
    Conversion.Balanced (recurringInterface (.var 0) r) ∧ ¬ Available (services r) missing ∧
    ¬ Idle (services r) missing ∧ ∀ q, ¬ PiCalculus.Step missing q := by
  refine ⟨missing_typed r, recurring_balanced (.var 0) r, ?_, ?_, ?_⟩
  · intro ha
    exact (ha 710 (senderSignature r) (sender_declared r)).elim id id
  · intro hi
    exact hi.no_unguarded_output (show HasUnguardedOutput missing from Or.inl trivial)
  · intro q hs
    have hinput := Endpoint.Step.source_hasUnguardedInput hs
    simp [missing, HasUnguardedInput, senderRequest, receiverRequest] at hinput

end Cslib.SessionTypes.Endpoint.RuntimeProgressTests
