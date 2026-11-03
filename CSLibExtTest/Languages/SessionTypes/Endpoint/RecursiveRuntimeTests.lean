/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveRepeatability
import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCong

/-!
# Actual recursive runtime: both roles, repeated session actions and real offers

These actual runtime consumers include general structural congruence.
General runtime Step preservation is supplied by RuntimeReduction;
qualified global runtime progress remains open.
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeTests

open PiCalculus Endpoint.Runtime

private theorem fresh : EndpointFresh (.var 0) := by
  constructor <;> intro h <;> cases h

/-- BOTH role orientations have six ACTUAL Steps and typed states, ending at the
same pending replicated code rather than a freshly allocated finite session. -/
theorem both_roles_six_steps (r : Role) :
    ∃ f : Fin 7 → Proc,
      f ⟨0, by decide⟩ = pending (.var 0) ∧ f ⟨6, by decide⟩ = pending (.var 0) ∧
      (∀ i : Fin 6, PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      (∀ i, Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) (f i)) ∧
      ∀ j : Fin 2,
        f ⟨3 * j.val + 2, by omega⟩ = bothInvoked (.var 0) ∧
        f ⟨3 * j.val + 3, by omega⟩ = pending (.var 0) :=
  typed_repeatable_trace r (.var 0) (Nat.zero_lt_succ 0) fresh 1

/-- Nonempty actual service syntax, not mere declared permissions, is offered. -/
theorem actual_offers (r : Role) (i : Nat) :
    Offered (services r) (phase (.var 0) i) 710 (senderSignature r) ∧
      Offered (services r) (phase (.var 0) i) 711 (receiverSignature r) :=
  phase_offers (.var 0) r i

/-- The typing-derived replicated service inversion itself supplies an actual offer. -/
theorem typed_sender_offer (r : Role) : ∃ sig, Offered (services r) senderDaemon 710 sig :=
  (sender_daemon_typed 0 r).service_offered

/-- Both orientations also execute on a genuine private Pi name, with empty
external ownership. Negative sender uses the positive bound cap's literal dual. -/
theorem closed_phases (r : Role) (i : Nat) :
    Runtime.HasType 0 (services r) ∅ (.nu (phase (.var 0) i)) := by
  have ht := phase_typed r (.var 0) (Nat.zero_lt_succ 0) fresh i
  cases r with
  | positive =>
    apply Runtime.HasType.nu (c := recurringCap) (separated_empty _)
    rw [Context.bind_empty]
    exact ht
  | negative =>
    apply Runtime.HasType.nu (c := recurringCap.dual) (separated_empty _)
    rw [Context.bind_empty, Capability.dual_dual]
    have hd : Finmap.Disjoint
        (Finmap.singleton (⟨.var 0, .positive⟩ : Key) recurringCap.dual : Context)
        (Finmap.singleton ⟨.var 0, .negative⟩ recurringCap) := by
      simp [Finmap.Disjoint, Finmap.mem_singleton]
    rw [Finmap.union_comm_of_disjoint hd]
    exact ht

/-- Private Steps wrap the SAME actual trace; no alternative runtime transition exists. -/
theorem closed_step (i : Nat) :
    PiCalculus.Step (.nu (phase (.var 0) i)) (.nu (phase (.var 0) (i + 1))) :=
  PiCalculus.Step.nu (phase_step (.var 0) i)

/-- Two different trace positions are genuine session actions on the SAME bound name. -/
theorem more_than_one_session_action :
    PiCalculus.Step (.nu (phase (.var 0) 2)) (.nu (phase (.var 0) 3)) ∧
      PiCalculus.Step (.nu (phase (.var 0) 5)) (.nu (phase (.var 0) 6)) ∧
      phase (.var 0) 3 = pending (.var 0) ∧ phase (.var 0) 6 = pending (.var 0) :=
  ⟨closed_step 2, closed_step 5, (session_round_phase (.var 0) 0).2.1,
    (session_round_phase (.var 0) 1).2.1⟩

/-- Real repl_unfold preserves EMPTY capture for this concrete service template:
accepting copy and persistent copy both own zero captured linear capabilities. -/
theorem sender_unfold_typed (r : Role) :
    Cong senderDaemon (.par (.inp (.const 710) (senderWorker (.var 0))) senderDaemon) ∧
      Runtime.HasType 0 (services r) ∅
        (.par (.inp (.const 710) (senderWorker (.var 0))) senderDaemon) := by
  refine ⟨Cong.repl_unfold _, ?_⟩
  exact (Runtime.HasType.cong_iff (Cong.repl_unfold _)).mp (sender_daemon_typed 0 r)

/-- The same actual interface retains BOTH role slots, literal rank7 and raw loop code. -/
theorem actual_linear_metadata (r : Role) :
    (recurringInterface (.var 0) r).lookup ⟨.var 0, r⟩ = some recurringCap ∧
      (recurringInterface (.var 0) r).lookup ⟨.var 0, r.opposite⟩ = some recurringCap.dual ∧
      recurringCap.rank = 7 ∧ recurringCap.protocol = recurringProtocol := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [recurringInterface, Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl),
      Finmap.lookup_singleton_eq]
  · rw [recurringInterface, Finmap.lookup_union_right (by
      cases r <;> simp [Finmap.mem_singleton, Role.opposite]), Finmap.lookup_singleton_eq]

/-- Substituting an actual outer var1 retains it as var2 under the worker's inner input. -/
theorem receiver_nested_capture_equation :
    PiCalculus.subst (receiverWorker (.var 0)) (.var 1) =
      .inp (.var 1) (.out (.const 711) (.var 2) .nil) := rfl

/-- The SAME six-edge witness contains BOTH marked session edges, with ownership
at every state. Separate copies of a Step proof cannot satisfy this trace shape. -/
theorem witnessed_two_session_rounds (r : Role) :
    ∃ f : Fin 7 → Proc,
      f ⟨0, by decide⟩ = pending (.var 0) ∧ f ⟨6, by decide⟩ = pending (.var 0) ∧
      (∀ i : Fin 6, PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      (∀ i, Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) (f i)) ∧
      f ⟨2, by decide⟩ = bothInvoked (.var 0) ∧ f ⟨3, by decide⟩ = pending (.var 0) ∧
      f ⟨5, by decide⟩ = bothInvoked (.var 0) := by
  refine ⟨fun i => phase (.var 0) i.val, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · intro i
    exact phase_step (.var 0) i.val
  · intro i
    exact phase_typed r (.var 0) (Nat.zero_lt_succ 0) fresh i.val

end Cslib.SessionTypes.Endpoint.RuntimeTests
