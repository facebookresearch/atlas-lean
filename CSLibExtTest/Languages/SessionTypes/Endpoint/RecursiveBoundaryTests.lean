/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveRepeatability
import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveQuiescence

/-!
# Captured-linear, missing-service and quiescence boundaries

Declared shared permissions alone do not supply actual offerings. Idle offered
services are not Cong nil. These counterexamples delimit future qualified progress.
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeBoundaryTests

open PiCalculus Endpoint.Runtime

/-- A nonempty ACTIVE ambient singleton is rejected by actual replication inversion.
Completed ambient annotations are intentionally permitted and are not BODY capture. -/
theorem captured_context_rejected (n : Nat) (r : Role) (b : Name) (c : Capability)
    (hactive : c.protocol.unfold ≠ .done) :
    ¬ Runtime.HasType n (services r) (Finmap.singleton (⟨b, r⟩ : Key) c) senderDaemon := by
  intro h
  exact hactive (h.repl_completed ⟨b, r⟩ c Finmap.lookup_singleton_eq)

/-- This replicated body tries to use a FREE linear subject instead of its received one. -/
def capturedSubject : Proc :=
  .repl (.inp (.const 710) (.out (.const 900) (.const 712) .nil))

/-- A body cannot acquire captured subject900 merely from shared permissions or scope. -/
theorem captured_subject_rejected (n : Nat) (r : Role) :
    ¬ Runtime.HasType n (services r) ∅ capturedSubject := by
  intro h
  obtain ⟨sig, he, hs, hp⟩ := h.service_inv
  rcases hp.output_subject with ⟨e, c, hn, hc⟩ | ⟨s, sig', hn, hc⟩
  · have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst e
    cases hn
  · have he := Name.const.inj hn
    subst s
    have hnone : (services r).lookup 900 = none := Finmap.lookup_eq_none.mpr
      (by simp [services, Finmap.mem_insert, Finmap.mem_singleton])
    rw [hnone] at hc
    cases hc

/-- Same physical name but WRONG actual payload role cannot invoke the sender service. -/
theorem wrong_role_rejected (n : Nat) (r : Role) (b : Name) :
    ¬ Runtime.HasType n (services r)
      (Finmap.singleton (⟨b, r.opposite⟩ : Key) recurringCap) (senderRequest b) := by
  intro h
  obtain ⟨e, v, hn, hv, hr, he, hg, hp⟩ := h.invoke_inv (sender_declared r)
  have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst e
  cases r <;> cases hr

/-- Tree equivalence does not repair an actual enclosing payload-rank mismatch. -/
theorem wrong_rank_rejected (n : Nat) (r : Role) (b : Name) :
    ¬ Runtime.HasType n (services r)
      (Finmap.singleton (⟨b, r⟩ : Key) (⟨8, recurringProtocol⟩ : Capability))
      (senderRequest b) := by
  intro h
  obtain ⟨e, v, hn, hv, hr, he, hg, hp⟩ := h.invoke_inv (sender_declared r)
  have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst e
  rw [Finmap.lookup_singleton_eq] at hv
  cases hv
  cases he.1

/-- Correct role and rank with the WRONG actual recursive direction is rejected. -/
theorem wrong_protocol_rejected (n : Nat) (r : Role) (b : Name) :
    ¬ Runtime.HasType n (services r)
      (Finmap.singleton (⟨b, r⟩ : Key) recurringCap.dual) (senderRequest b) := by
  intro h
  obtain ⟨e, v, hn, hv, hr, he, hg, hp⟩ := h.invoke_inv (sender_declared r)
  have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst e
  rw [Finmap.lookup_singleton_eq] at hv
  cases hv
  cases he.2.head

/-- Shared priority has NO identical-payload-key exemption: equality7<7 fails. -/
theorem equal_service_priority_rejected (n : Nat) (r : Role) (b : Name) :
    ¬ Runtime.HasType n (Finmap.singleton 710 (⟨7, r, recurringCap⟩ : ServiceSignature))
      (Finmap.singleton (⟨b, r⟩ : Key) recurringCap) (senderRequest b) := by
  intro h
  obtain ⟨e, v, hn, hv, hr, he, hg, hp⟩ := h.invoke_inv Finmap.lookup_singleton_eq
  have hk := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst e
  rw [Finmap.lookup_singleton_eq] at hv
  cases hv
  have hlt := hg ⟨b, r⟩ recurringCap Finmap.lookup_singleton_eq (by
    change recurringProtocol.unfold ≠ .done
    rw [recurring_unfold]
    intro h
    cases h)
  exact Nat.lt_irrefl 7 hlt

/-- Both signatures are declared, but NEITHER actual daemon is present. -/
def missingServices : Proc := .par (senderRequest (.var 0)) (receiverRequest (.var 0))

/-- Typed requests do not imply actual service availability. Both orientations admit them. -/
theorem missing_services_typed (r : Role) :
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) missingServices := by
  apply Runtime.HasType.par
  · cases r <;> simp [Finmap.Disjoint, Finmap.mem_singleton, Role.opposite]
  · exact sender_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h)
  · exact receiver_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h)

/-- Missing actual services leave these typed requests stuck under FULL canonical Step. -/
theorem missing_services_no_step (q : Proc) : ¬ PiCalculus.Step missingServices q := by
  intro h
  have hi := Endpoint.Step.source_hasUnguardedInput h
  simp [HasUnguardedInput, missingServices, senderRequest, receiverRequest] at hi

/-- The absent daemon cannot be inferred from the declaration or requested endpoint. -/
theorem missing_services_not_offered (r : Role) (s : Nat) (sig : ServiceSignature) :
    ¬ Offered (services r) missingServices s sig := by
  intro h
  exact h.2.elim (fun h => h) (fun h => h)

/-- Unavailable services can block even an EMPTY-interface typed private network. -/
theorem closed_missing_typed :
    Runtime.HasType 0 (services .positive) ∅ (.nu missingServices) := by
  apply Runtime.HasType.nu (c := recurringCap) (separated_empty _)
  rw [Context.bind_empty]
  exact missing_services_typed .positive

/-- A private binder does not create the missing input daemon. -/
theorem closed_missing_no_step (q : Proc) : ¬ PiCalculus.Step (.nu missingServices) q := by
  intro h
  have hi := Endpoint.Step.source_hasUnguardedInput h
  simp [HasUnguardedInput, missingServices, senderRequest, receiverRequest] at hi

/-- Stuck pending requests are not the finite completion branch either. -/
theorem closed_missing_not_nil : ¬ Cong (.nu missingServices) .nil := by
  intro h
  have ho := (output_cong h).mp (show HasUnguardedOutput (.nu missingServices) from Or.inl trivial)
  exact ho

/-- Actual offered but waiting daemons, with no pending requests. -/
def idleServices : Proc := .par senderDaemon receiverDaemon

/-- Idle daemons really are typed with EMPTY captured ownership in both orientations. -/
theorem idle_typed (r : Role) : Runtime.HasType 0 (services r) ∅ idleServices := by
  simpa [idleServices] using Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context))
    (sender_daemon_typed 0 r) (receiver_daemon_typed 0 r)

/-- Idle is computed from literal declared-input service syntax, not a future-trace field. -/
theorem idle_static (r : Role) : Idle (services r) idleServices :=
  ⟨⟨710, rfl, Finmap.mem_of_lookup_eq_some (sender_declared r)⟩,
    ⟨711, rfl, Finmap.mem_of_lookup_eq_some (receiver_declared r)⟩⟩

/-- Both idle daemons are actual unguarded replicated offers. -/
theorem idle_offers (r : Role) :
    Offered (services r) idleServices 710 (senderSignature r) ∧
      Offered (services r) idleServices 711 (receiverSignature r) :=
  ⟨⟨sender_declared r, Or.inl rfl⟩, ⟨receiver_declared r, Or.inr rfl⟩⟩

/-- Idle but offered services cannot reduce until a request arrives. -/
theorem idle_no_step (r : Role) (q : Proc) : ¬ PiCalculus.Step idleServices q :=
  (idle_static r).no_step q

/-- Waiting services are NOT Cong nil, despite genuinely empty linear ownership. -/
theorem idle_not_nil : ¬ Cong idleServices .nil := by
  intro h
  have hi := (input_cong h).mp (show HasUnguardedInput idleServices from Or.inl trivial)
  exact hi

end Cslib.SessionTypes.Endpoint.RuntimeBoundaryTests
