/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveReduction

/-!
# Actual multiple persistent services and nested template reductions
-/

namespace Cslib.SessionTypes.Endpoint.PersistentOfferTests

open PiCalculus Endpoint.Runtime

private def wrappedSender : Proc :=
  .repl (.par (.inp (.const 710) (senderWorker (.var 0))) .nil)
private def nestedReceiver : Proc := .repl receiverDaemon
private def start : Proc :=
  .par (.par (senderRequest (.var 0)) wrappedSender)
    (.par (receiverRequest (.var 0)) nestedReceiver)
private def middle : Proc :=
  .par (.par (senderWorker (.var 0)) wrappedSender)
    (.par (receiverRequest (.var 0)) nestedReceiver)
private def finish : Proc :=
  .par (.par (senderWorker (.var 0)) wrappedSender)
    (.par (.par (receiverWorker (.var 0)) receiverDaemon) nestedReceiver)

private theorem wrapper_cong : Cong senderDaemon wrappedSender :=
  Cong.repl_cong (Cong.par_nil (.inp (.const 710) (senderWorker (.var 0)))).symm

private theorem start_typed (r : Role) : Runtime.HasType 1 (services r)
    (recurringInterface (.var 0) r) start := by
  have hsender := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he)
    (sender_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h))
    ((Runtime.HasType.cong_iff wrapper_cong).mp (sender_daemon_typed 1 r))
  have hnested : Runtime.HasType 1 (services r) ∅ nestedReceiver := Runtime.HasType.serve
    ⟨711, rfl, Finmap.mem_of_lookup_eq_some (receiver_declared r)⟩
    (receiver_daemon_typed 1 r) Context.completed_empty
    (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty _)
  have hreceiver := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he)
    (receiver_request_typed r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h)) hnested
  simp only [Finmap.union_empty] at hsender hreceiver
  apply Runtime.HasType.par ?_ hsender hreceiver
  cases r <;> simp [Finmap.Disjoint, Finmap.mem_singleton, Role.opposite]

private theorem wrapped_step (b : Name) :
    PiCalculus.Step (.par (senderRequest b) wrappedSender) (.par (senderWorker b) wrappedSender) :=
  PiCalculus.Step.cong (Cong.par_cong (Cong.refl _) wrapper_cong.symm)
    (service_invocation_step 710 b (senderWorker (.var 0)))
    (Cong.par_cong (Cong.refl _) wrapper_cong)

private theorem nested_step (b : Name) : PiCalculus.Step (.par (receiverRequest b) nestedReceiver)
    (.par (.par (receiverWorker b) receiverDaemon) nestedReceiver) := by
  exact PiCalculus.Step.cong
    (Cong.trans (Cong.par_cong (Cong.refl _) (Cong.repl_unfold receiverDaemon))
      (Cong.symm (Cong.par_assoc (receiverRequest b) receiverDaemon nestedReceiver)))
    (PiCalculus.Step.parL (service_invocation_step 711 b (receiverWorker (.var 0)))) (Cong.refl _)

private theorem start_step : PiCalculus.Step start middle :=
  PiCalculus.Step.parL (wrapped_step (.var 0))
private theorem middle_step : PiCalculus.Step middle finish :=
  PiCalculus.Step.parR (nested_step (.var 0))

private theorem start_available (r : Role) : Available (services r) start := by
  intro s sig hs
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hs) with he | he
  · subst s
    simp [start, wrappedSender, nestedReceiver, receiverDaemon, OfferedIn, AcceptIn]
  · have heq := (Finmap.mem_singleton _ _ _).mp he
    subst s
    simp [start, wrappedSender, nestedReceiver, receiverDaemon, OfferedIn, AcceptIn]

/-- TWO real calls consume accepting copies under nil/nested-replica wrappers.
GENERAL runtime preservation types all states at the same actual loop interface;
GENERAL syntax-only offer closure retains EVERY declared signature in all states. -/
theorem no_loss_two_real_calls (r : Role) :
    PiCalculus.Step start middle ∧ PiCalculus.Step middle finish ∧
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) start ∧
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) middle ∧
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) finish ∧
    Available (services r) start ∧ Available (services r) middle ∧
    Available (services r) finish := by
  have hm := recurring_step_preserved r (.var 0) (start_typed r) start_step
  have hf := recurring_step_preserved r (.var 0) hm middle_step
  have ha := (start_available r).step start_step
  exact ⟨start_step, middle_step, start_typed r, hm, hf, start_available r, ha, ha.step middle_step⟩

/-- After ANY finite canonical reduction from the populated nested-service source,
all original declared signatures remain syntactically persistently available. -/
theorem finite_calls_keep_available (r : Role) {q : Proc}
    (hr : Relation.ReflTransGen PiCalculus.Step start q) : Available (services r) q :=
  (start_available r).reachable hr

/-- The invariant is MONOTONE, not equality: a hidden replicated continuation
may become a new persistent offer after communication. This syntax-only example
uses no typing premise and does not infer availability from a declaration alone. -/
theorem new_continuation_offer (r : Role) :
    ¬ OfferedIn 711 (.par (.out (.const 900) (.const 901) receiverDaemon)
      (.inp (.const 900) .nil)) ∧
    PiCalculus.Step (.par (.out (.const 900) (.const 901) receiverDaemon) (.inp (.const 900) .nil))
      (.par receiverDaemon .nil) ∧
    Offered (services r) (.par receiverDaemon .nil) 711 (receiverSignature r) :=
  ⟨fun h => h.elim id id, PiCalculus.Step.commSelect (Select.refl _) (Select.refl _),
    receiver_declared r, Or.inl rfl⟩

end Cslib.SessionTypes.Endpoint.PersistentOfferTests
