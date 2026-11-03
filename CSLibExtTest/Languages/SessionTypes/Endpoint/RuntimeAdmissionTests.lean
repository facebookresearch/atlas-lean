/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCong
import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeEnvironmentWeakening
import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveRepeatability
import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveQuiescence

/-!
# Completed ambient, structural template and namespace admission consumers

Former empty-ambient structural boundaries are positive; actual active capture,
unguarded output replication and shared-name ownership aliases remain negative.
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeAdmissionTests

open PiCalculus Endpoint.Runtime

private def doneFrame : Context := Finmap.singleton ⟨.var 0, .positive⟩ ⟨3, .done⟩

private theorem daemon_frame (r : Role) :
    Runtime.HasType 1 (services r) doneFrame senderDaemon := by
  exact (sender_daemon_typed 1 r).weaken_completed Finmap.notMem_empty rfl
    (Nat.zero_lt_succ 0) (by intro s sig hs hn; cases hn)

private theorem unused_restriction (p : Proc) : Cong p (.nu (liftProc 0 p)) := by
  apply Cong.trans (Cong.symm (Cong.par_nil p))
  apply Cong.trans (Cong.par_comm p .nil)
  apply Cong.trans (Cong.par_cong Cong.nu_nil.symm (Cong.refl p))
  apply Cong.trans (Cong.scope .nil p)
  exact Cong.nu_cong (Cong.trans (Cong.par_comm .nil _) (Cong.par_nil _))

/-- External completed annotations survive parallel nil elimination and its converse. -/
theorem completed_external_ambient (r : Role) :
    Runtime.HasType 1 (services r) doneFrame (.par senderDaemon .nil) ∧
      Runtime.HasType 1 (services r) doneFrame senderDaemon :=
  ⟨(Runtime.HasType.cong_iff (Cong.par_nil senderDaemon)).mpr (daemon_frame r), daemon_frame r⟩

/-- The genuinely unused private pair is now admitted through GENERAL Cong. -/
theorem unused_private_daemon (r : Role) :
    Runtime.HasType 1 (services r) doneFrame (.nu (liftProc 0 senderDaemon)) :=
  (Runtime.HasType.cong_iff (unused_restriction senderDaemon)).mp (daemon_frame r)

private def wrapped : Proc :=
  .repl (.par (.inp (.const 710) (senderWorker (.var 0))) .nil)

private theorem wrapped_cong : Cong senderDaemon wrapped :=
  Cong.repl_cong (Cong.par_nil (.inp (.const 710) (senderWorker (.var 0)))).symm

/-- Nil inside the replicated guarded template does not capture the ambient frame. -/
theorem guarded_wrapper_typed (r : Role) : Runtime.HasType 1 (services r) doneFrame wrapped :=
  (Runtime.HasType.cong_iff wrapped_cong).mp (daemon_frame r)

/-- The BODY of an annotated guarded replica remains EXACT EMPTY. -/
theorem guarded_wrapper_body_empty (r : Role) :
    Runtime.HasType 1 (services r) ∅ (.par (.inp (.const 710) (senderWorker (.var 0))) .nil) :=
  (guarded_wrapper_typed r).repl_body_empty.2

/-- Actual offers and static Idle survive the same structural wrapper. -/
theorem guarded_wrapper_offered_idle (r : Role) :
    Offered (services r) wrapped 710 (senderSignature r) ∧ Idle (services r) wrapped := by
  have hoff : Offered (services r) senderDaemon 710 (senderSignature r) := ⟨sender_declared r, rfl⟩
  have hidle : Idle (services r) senderDaemon :=
    ⟨710, rfl, Finmap.mem_of_lookup_eq_some (sender_declared r)⟩
  exact ⟨(Offered.cong_iff wrapped_cong).mp hoff, (Idle.cong_iff wrapped_cong).mp hidle⟩

/-- Nested replicas and a private wrapper INSIDE replication are actual guarded shapes. -/
theorem nested_templates_typed (r : Role) :
    Runtime.HasType 1 (services r) doneFrame (.repl senderDaemon) ∧
      Runtime.HasType 1 (services r) doneFrame
        (.repl (.nu (liftProc 0 (.inp (.const 710) (senderWorker (.var 0)))))) := by
  have ht : ServiceTemplate (services r) senderDaemon :=
    ⟨710, rfl, Finmap.mem_of_lookup_eq_some (sender_declared r)⟩
  refine ⟨Runtime.HasType.serve ht (sender_daemon_typed 1 r)
    (daemon_frame r).repl_completed (daemon_frame r).context_closedAt
    (daemon_frame r).separated, ?_⟩
  exact (Runtime.HasType.cong_iff (Cong.repl_cong
    (unused_restriction (.inp (.const 710) (senderWorker (.var 0)))))).mp (daemon_frame r)

/-- An unguarded active output is never a service template, even if zero resources
could be alleged for its BODY. The syntactic guard test rejects it first. -/
theorem unguarded_output_replica_rejected {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    (a b : Name) (p : Proc) : ¬ Runtime.HasType n Γ Δ (.repl (.out a b p)) := by
  intro h
  exact h.repl_body_empty.1

private def aliasName : Name → Name
  | .var 0 => .const 710
  | a => a

/-- Fixing declared constants does not supply the independently required owned-image nonalias. -/
theorem fixed_shared_not_nonalias (r : Role) :
    FixesShared (services r) aliasName ∧
      ¬ NonAliases (services r) (Finmap.singleton ⟨.var 0, r⟩ recurringCap) aliasName := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro h
  exact h ⟨.var 0, r⟩ ((Finmap.mem_singleton _ _ _).mpr rfl) 710 (senderSignature r)
    (sender_declared r) rfl

private theorem fresh_extension (r : Role) (t : Nat) (sig : ServiceSignature)
    (ht : t ≠ 710) (hu : t ≠ 711) : EnvExtends (services r) ((services r).insert t sig) := by
  intro s v hs
  have hne : s ≠ t := by
    intro h
    subst s
    have hm := Finmap.mem_of_lookup_eq_some hs
    simp only [services, Finmap.mem_insert, Finmap.mem_singleton] at hm
    exact hm.elim hu ht
  rw [Finmap.lookup_insert_of_ne _ hne]
  exact hs

/-- Fresh Γ-extension admits harmless PASSIVE data uses of the newly shared
constant712. An all-position NameAbsent premise would incorrectly reject this. -/
theorem passive_new_shared_constant (r : Role) :
    Runtime.HasType 1 ((services r).insert 712 (senderSignature r))
      (Finmap.singleton ⟨.var 0, r⟩ recurringCap) (senderWorker (.var 0)) ∧
      ¬ NameAbsent (.const 712) (senderWorker (.var 0)) := by
  refine ⟨?_, fun h => h.2.1 rfl⟩
  apply (sender_worker_typed r (.var 0) (Nat.zero_lt_succ 0)
    (by constructor <;> intro h <;> cases h)).env_extend
      (fresh_extension r 712 (senderSignature r) (by decide) (by decide))
  exact separated_singleton (by intro s sig hs hn; cases hn)

/-- Literal signature extension still cannot alias an ACTUAL OWNED constant,
even when its capability is done: separation is required for completed entries too. -/
theorem new_shared_owned_alias (r : Role) :
    EnvExtends (services r) ((services r).insert 900 (senderSignature r)) ∧
      Runtime.HasType 0 (services r)
        (Finmap.singleton ⟨.const 900, r⟩ (⟨3, .done⟩ : Capability)) senderDaemon ∧
      ¬ Runtime.HasType 0 ((services r).insert 900 (senderSignature r))
        (Finmap.singleton ⟨.const 900, r⟩ (⟨3, .done⟩ : Capability)) senderDaemon := by
  refine ⟨fresh_extension r 900 (senderSignature r) (by decide) (by decide), ?_, ?_⟩
  · apply (sender_daemon_typed 0 r).weaken_completed
      (z := ⟨.const 900, r⟩) (u := ⟨3, .done⟩) Finmap.notMem_empty rfl trivial
    intro s sig hs hn
    have he := Name.const.inj hn
    subst s
    have hm := Finmap.mem_of_lookup_eq_some hs
    simp [services, Finmap.mem_insert, Finmap.mem_singleton] at hm
  · intro h
    exact h.separated ⟨.const 900, r⟩ ⟨3, .done⟩ Finmap.lookup_singleton_eq
      900 (senderSignature r) (Finmap.lookup_insert _) rfl

/-- The finite embedding is a genuine ALL7-rule bridge, at unchanged actual Γ/Δ/p. -/
theorem finite_embedding {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : Conversion.RankedType n Δ p) (hs : Separated Γ Δ) : Runtime.HasType n Γ Δ p :=
  Runtime.HasType.of_finite h hs

/-- Completed ambient annotations survive actual scope extrusion, its reverse,
and real replica unfolding at the SAME interface. -/
theorem completed_scope_and_unfold (r : Role) :
    Runtime.HasType 1 (services r) doneFrame
      (.nu (.par (liftProc 0 senderDaemon) (liftProc 0 receiverDaemon))) ∧
    Runtime.HasType 1 (services r) doneFrame
      (.par (.nu (liftProc 0 senderDaemon)) receiverDaemon) ∧
    Runtime.HasType 1 (services r) doneFrame
      (.par (.inp (.const 710) (senderWorker (.var 0))) senderDaemon) := by
  have hsource := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he)
    (unused_private_daemon r) (receiver_daemon_typed 1 r)
  simp only [Finmap.union_empty] at hsource
  exact ⟨hsource.scope_forward, hsource,
    (Runtime.HasType.cong_iff (Cong.repl_unfold _)).mp (daemon_frame r)⟩

/-- Two actual private wrappers may swap through canonical capture-safe transport,
including their completed ambient context and exact literal bound pairs. -/
theorem completed_private_swap (r : Role) : Runtime.HasType 1 (services r) doneFrame
    (.nu (.nu (swapProc 0 senderDaemon))) := by
  have hfirst := unused_private_daemon r
  have hsecond := (Runtime.HasType.cong_iff
    (unused_restriction (.nu (liftProc 0 senderDaemon)))).mp hfirst
  have hshape : liftProc 0 (.nu (liftProc 0 senderDaemon)) = .nu senderDaemon := rfl
  rw [hshape] at hsecond
  exact (Runtime.HasType.cong_iff (Cong.nu_swap senderDaemon)).mp hsecond

end Cslib.SessionTypes.Endpoint.RuntimeAdmissionTests
