/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeSharedHead
import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCong
import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveOwnership

/-!
# Actual endpoint delegation followed by shared recursive invocation

Both payload roles use an unfolded code unequal to the advertised regular code.
The process substrate and Steps remain the canonical π calculus.
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeDelegationTests

open PiCalculus Endpoint.Runtime

private def actualCap : Capability := ⟨7, recurringProtocol.unfold⟩
private def doneCarrier : Capability := ⟨1, .done⟩
private def outCarrier (r : Role) : Capability := ⟨1, .sendEndpoint r 7 recurringProtocol .done⟩
private def inCarrier (r : Role) : Capability := ⟨1, .recvEndpoint r 7 recurringProtocol .done⟩
private def payloadKey (r : Role) : Key := ⟨.var 1, r⟩
private def outKey : Key := ⟨.var 0, .positive⟩
private def inKey : Key := ⟨.var 0, .negative⟩
private def senderContext (r : Role) : Context :=
  (Finmap.singleton (payloadKey r) actualCap).insert outKey (outCarrier r)
private def receiverContext (r : Role) : Context := Finmap.singleton inKey (inCarrier r)
private def advancedContext (r : Role) : Context :=
  ((Finmap.singleton (payloadKey r) actualCap).insert outKey doneCarrier).insert inKey doneCarrier

private theorem actual_equivalent : actualCap.Equivalent recurringCap :=
  ⟨rfl, (Protocol.treeEquiv_unfold recurringProtocol).symm⟩

/-- The actual raw code is unequal, while role/rank/regular-tree comparison is exact. -/
theorem unequal_actual_payload_code :
    actualCap.protocol ≠ recurringCap.protocol ∧ actualCap.Equivalent recurringCap := by
  refine ⟨?_, actual_equivalent⟩
  change recurringProtocol.unfold ≠ recurringProtocol
  rw [recurring_unfold]
  intro h
  cases h

private theorem received_body (r : Role) : Runtime.HasType 3 (services r)
    ((Context.lift 0 ((receiverContext r).insert inKey doneCarrier)).insert
      ⟨.var 0, r⟩ recurringCap) (senderRequest (.var 0)) := by
  have h := (sender_request_typed r (.var 0) (Nat.zero_lt_succ 2)
    (by constructor <;> intro h <;> cases h)).weaken_completed
      (z := ⟨.var 1, .negative⟩) (u := doneCarrier)
      (by simp [Finmap.mem_singleton]) rfl (show 1 < 3 by decide)
      (by intro s sig hs hn; cases hn)
  have hne : (⟨.var 0, r⟩ : Key) ≠ ⟨.var 1, .negative⟩ := by
    intro h
    cases h
  rw [receiverContext, Finmap.insert_singleton_eq, Context.lift_singleton]
  change Runtime.HasType 3 (services r)
    ((Finmap.singleton (⟨.var 1, .negative⟩ : Key) doneCarrier).insert ⟨.var 0, r⟩ recurringCap) _
  change Runtime.HasType 3 (services r)
    (((∅ : Context).insert ⟨.var 1, .negative⟩ doneCarrier).insert ⟨.var 0, r⟩ recurringCap) _
  rw [Finmap.insert_insert_of_ne (s := (∅ : Context)) hne.symm]
  exact h

private theorem input_typed (r : Role) : Runtime.HasType 2 (services r) (receiverContext r)
    (.inp (.var 0) (senderRequest (.var 0))) := by
  apply Runtime.HasType.inpEndpoint (e := inKey) (c := inCarrier r)
    (r := r) (k := 7) (t := recurringProtocol) (s := .done)
    (guardMin_singleton _ _) (separated_singleton (by intro s sig hs hn; cases hn))
    Finmap.lookup_singleton_eq rfl (Nat.zero_lt_succ 1)
  exact received_body r

private theorem output_typed (r : Role) : Runtime.HasType 2 (services r) (senderContext r)
    (.out (.var 0) (.var 1) .nil) := by
  have hne : outKey ≠ payloadKey r := by intro h; cases h
  apply Runtime.HasType.outEndpoint (e := outKey) (d := payloadKey r)
    (c := outCarrier r) (v := actualCap) (k := 7) (t := recurringProtocol) (s := .done)
  · intro d c hc ha hde
    rw [senderContext, Finmap.lookup_insert_of_ne _ hde] at hc
    have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst d
    rw [Finmap.lookup_singleton_eq] at hc
    cases hc
    exact (by decide : 1 < 7)
  · apply Separated.insert
    · exact separated_singleton (by intro s sig hs hn; cases hn)
    · intro s sig hs hn
      cases hn
  · exact Finmap.lookup_insert _
  · rfl
  · rw [senderContext, Finmap.lookup_insert_of_ne _ hne.symm]
    exact Finmap.lookup_singleton_eq
  · exact actual_equivalent
  · exact hne
  · exact Nat.zero_lt_succ 1
  · exact (by decide : 1 < 2)
  · rw [senderContext, Context.erase_insert_ne hne, erase_singleton, Finmap.insert_insert]
    apply Runtime.HasType.nil (Context.completed_empty.insert (by rfl))
    · intro e he
      rcases Finmap.mem_insert.mp he with rfl | he
      · exact Nat.zero_lt_succ 1
      · exact False.elim (Finmap.notMem_empty he)
    · exact (separated_empty _).insert outKey doneCarrier
        (by intro s sig hs hn; cases hn)

/-- BOTH payload roles delegate on the existing linear carrier and continue with
an actual shared invocation, a continuation impossible in the old finite-wrapper API. -/
theorem delegate_then_invoke_typed (r : Role) :
    Runtime.HasType 2 (services r) (senderContext r) (.out (.var 0) (.var 1) .nil) ∧
      Runtime.HasType 2 (services r) (receiverContext r)
        (.inp (.var 0) (senderRequest (.var 0))) := ⟨output_typed r, input_typed r⟩

private theorem real_split (r : Role) : Finmap.Disjoint (senderContext r) (receiverContext r) := by
  intro e he ht
  have heq := (Finmap.mem_singleton _ _ _).mp ht
  subst e
  simp [senderContext, outKey, inKey, payloadKey,
    Finmap.mem_insert, Finmap.mem_singleton] at he

/-- The actual recoded payload, BOTH roles, is preserved through the received
binder by the GENERAL split-derived endpoint substitution theorem. -/
theorem actual_received_substitution (r : Role) : Runtime.HasType 2 (services r)
    (((receiverContext r).insert inKey doneCarrier).insert (payloadKey r) actualCap)
    (senderRequest (.var 1)) := by
  have ht := (received_body r).subst_endpoint_from_split (b := .var 1) (r := r)
    (v := actualCap) (e := inKey) (output_typed r).separated (real_split r)
    (by
      rw [senderContext, Finmap.lookup_insert_of_ne _ (by intro h; cases h)]
      exact Finmap.lookup_singleton_eq)
    (show (receiverContext r).lookup inKey = some (inCarrier r) from Finmap.lookup_singleton_eq)
    actual_equivalent (by decide : 1 < 2)
  exact ht

private theorem advanced_request (r : Role) : Runtime.HasType 2 (services r)
    (advancedContext r) (senderRequest (.var 1)) := by
  have hne : outKey ≠ inKey := by decide
  have hnp : outKey ≠ payloadKey r := by intro h; cases h
  have ht := (actual_received_substitution r).weaken_completed (z := outKey) (u := doneCarrier)
    (by simp [receiverContext, Finmap.mem_insert, Finmap.mem_singleton, hne, hnp])
    rfl (Nat.zero_lt_succ 1) (by intro s sig hs hn; cases hn)
  rw [receiverContext, Finmap.insert_singleton_eq] at ht
  change Runtime.HasType 2 (services r)
    ((((∅ : Context).insert inKey doneCarrier).insert (payloadKey r) actualCap).insert
      outKey doneCarrier) _ at ht
  rw [Finmap.insert_insert_of_ne (s := (∅ : Context))
    (a := inKey) (a' := payloadKey r) (by intro h; cases h),
    Finmap.insert_insert_of_ne (s := (∅ : Context).insert (payloadKey r) actualCap)
      (a := inKey) (a' := outKey) hne.symm] at ht
  exact ht

/-- Shared head preserves the already advanced linear interface and actual recoded
payload even when BOTH carrier slots remain recorded as completed annotations. -/
theorem advanced_shared_head (r : Role) : Runtime.HasType 2 (services r)
    (advancedContext r) (senderWorker (.var 1)) := by
  have hinput := (sender_daemon_typed 2 r).repl_body_empty.2
  have ht := Runtime.HasType.shared_head (sender_declared r)
    (fun _ _ he => Finmap.notMem_empty he) (advanced_request r) hinput
  simp only [Finmap.union_empty, sender_subst] at ht
  exact (Runtime.HasType.cong_iff (Cong.trans (Cong.par_comm .nil _)
    (Cong.par_nil _))).mp ht

/-- Typed nested receive substitution retains var1 as var2 beneath the inner
passive binder, using the ACTUAL equivalent dual payload for BOTH role orientations. -/
theorem nested_actual_substitution (r : Role) : Runtime.HasType 2 (services r)
    (Finmap.singleton ⟨.var 1, r.opposite⟩ actualCap.dual)
    (.inp (.var 1) (.out (.const 711) (.var 2) .nil)) := by
  have hp := receiver_worker_typed r (.var 0) (Nat.zero_lt_succ 2)
    (by constructor <;> intro h <;> cases h)
  have hformal : Runtime.HasType 3 (services r)
      ((Context.lift 0 ∅).insert ⟨.var 0, r.opposite⟩ recurringCap.dual)
      (receiverWorker (.var 0)) := by
    rw [Context.lift_empty]
    have he : (∅ : Context).insert ⟨.var 0, r.opposite⟩ recurringCap.dual =
        Finmap.singleton ⟨.var 0, r.opposite⟩ recurringCap.dual := rfl
    rw [he]
    exact hp
  exact hformal.subst_endpoint actual_equivalent.dual (by decide : 1 < 2)
    Finmap.notMem_empty (by intro s sig hs hn; cases hn)

/-- TWO actual canonical Steps perform linear delegation, then invoke the existing
recursive service. Both orientations have populated typings before/after the linear
advance; the shared invocation retains the SAME advanced actual-value interface. -/
theorem actual_delegate_then_invoke_steps (r : Role) :
    Runtime.HasType 2 (services r) (senderContext r ∪ receiverContext r)
      (.par (.par (.out (.var 0) (.var 1) .nil)
        (.inp (.var 0) (senderRequest (.var 0)))) senderDaemon) ∧
    Runtime.HasType 2 (services r) (advancedContext r)
      (.par (senderRequest (.var 1)) senderDaemon) ∧
    Runtime.HasType 2 (services r) (advancedContext r)
      (.par (senderWorker (.var 1)) senderDaemon) ∧
    PiCalculus.Step
      (.par (.par (.out (.var 0) (.var 1) .nil)
        (.inp (.var 0) (senderRequest (.var 0)))) senderDaemon)
      (.par (senderRequest (.var 1)) senderDaemon) ∧
    PiCalculus.Step (.par (senderRequest (.var 1)) senderDaemon)
      (.par (senderWorker (.var 1)) senderDaemon) := by
  have hnil : Finmap.Disjoint (advancedContext r) ∅ := fun _ _ he => Finmap.notMem_empty he
  refine ⟨?_, ?_, ?_, ?_, service_invocation_step 710 (.var 1) (senderWorker (.var 0))⟩
  · have hsource := Runtime.HasType.par (real_split r) (output_typed r) (input_typed r)
    have h := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he) hsource
      (sender_daemon_typed 2 r)
    simpa only [Finmap.union_empty] using h
  · simpa only [Finmap.union_empty] using Runtime.HasType.par hnil (advanced_request r)
      (sender_daemon_typed 2 r)
  · simpa only [Finmap.union_empty] using Runtime.HasType.par hnil (advanced_shared_head r)
      (sender_daemon_typed 2 r)
  · exact PiCalculus.Step.cong (Cong.refl _)
      (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
      (Cong.par_cong (Cong.trans (Cong.par_comm .nil _) (Cong.par_nil _)) (Cong.refl _))

end Cslib.SessionTypes.Endpoint.RuntimeDelegationTests
