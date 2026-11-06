/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Context
public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Actual guarded recursive endpoint use via canonical replication triggers

The finite daemon code is independent of the endpoint name. Each invocation
receives one linear role, performs a session action, then transfers it back.
This module gives concrete canonical executions; RuntimeReduction and
RuntimeGlobalProgress establish the general runtime metatheorems.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Invoking a replicated service is a reduction step.**
Canonical replication unfolds and communicates on a real shared trigger. -/
theorem service_invocation_step (s : Nat) (b : Name) (body : Proc) :
    PiCalculus.Step (.par (.out (.const s) b .nil) (.repl (.inp (.const s) body)))
      (.par (PiCalculus.subst body b) (.repl (.inp (.const s) body))) := by
  apply PiCalculus.Step.cong
    (Cong.trans (Cong.par_cong (Cong.refl _) (Cong.repl_unfold _))
      (Cong.symm (Cong.par_assoc _ _ _)))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
  exact Cong.par_cong (Cong.trans (Cong.par_comm _ _) (Cong.par_nil _)) (Cong.refl _)

/-- **One-state recurring send graph.**
Every edge of this reachable one-state graph performs a session send. -/
def recurringGraph : Graph := ⟨1, fun _ => .sendName ⟨0, by decide⟩⟩

/-- **Recurring send protocol.** Initial cursor of the one-state recurring send protocol. -/
def recurringProtocol : Protocol := .regular recurringGraph ⟨0, by decide⟩ false

/-- **Fixed-rank capability of the recurring session.**
The recurring session keeps one literal static capability rank throughout. -/
def recurringCap : Capability := ⟨7, recurringProtocol⟩

/-- **The recurring protocol unfolds to a send of itself.**
Literal guarded self-loop unfolding, not an unreachable extra graph node. -/
theorem recurring_unfold : recurringProtocol.unfold = .sendName recurringProtocol := rfl

/-- **The dual recurring protocol unfolds to a receive of itself.**
The peer's literal guarded cursor returns to the same receive protocol. -/
theorem recurring_dual_unfold :
    recurringProtocol.dual.unfold = .recvName recurringProtocol.dual := rfl

/-- **Sender worker process.**
Worker code has one session action and a real endpoint-transfer reentry. -/
def senderWorker (b : Name) : Proc := .out b (.const 712) (.out (.const 710) b .nil)

/-- **Receiver worker process.**
A received session endpoint survives the worker's passive input binder. -/
def receiverWorker (b : Name) : Proc := .inp b (.out (.const 711) (liftName 0 b) .nil)

/-- **Replicated sender daemon.**
Sender replication captures only shared constants and its per-invocation formal. -/
def senderDaemon : Proc := .repl (.inp (.const 710) (senderWorker (.var 0)))

/-- **Replicated receiver daemon.**
Receiver replication likewise receives, rather than captures, its endpoint. -/
def receiverDaemon : Proc := .repl (.inp (.const 711) (receiverWorker (.var 0)))

/-- **Sender-role transfer to its trigger.**
Transfer the actual sender-role endpoint to its shared trigger. -/
def senderRequest (b : Name) : Proc := .out (.const 710) b .nil

/-- **Receiver-role transfer to its trigger.**
Transfer the actual opposite-role endpoint to its shared trigger. -/
def receiverRequest (b : Name) : Proc := .out (.const 711) b .nil

/-- **Pending state with two role transfers.**
Persistent services plus TWO pending role transfers, on one physical endpoint. -/
def pending (b : Name) : Proc := .par (.par (senderRequest b) senderDaemon)
  (.par (receiverRequest b) receiverDaemon)

/-- **State after the sender trigger invocation.**
After one trigger invocation, the opposite request and both daemons remain. -/
def sentInvoked (b : Name) : Proc := .par (.par (senderWorker b) senderDaemon)
  (.par (receiverRequest b) receiverDaemon)

/-- **State after both trigger invocations.**
Both received-role workers can now communicate on their actual session name. -/
def bothInvoked (b : Name) : Proc := .par (.par (senderWorker b) senderDaemon)
  (.par (receiverWorker b) receiverDaemon)

/-- **Substitution instantiates the sender worker's endpoint.**
Capture-safe first trigger communication instantiates the actual bound endpoint. -/
theorem sender_subst (b : Name) : PiCalculus.subst (senderWorker (.var 0)) b = senderWorker b := rfl

/-- **Substitution instantiates the receiver worker's endpoint.**
Receiver preserves the actual endpoint under its inner passive input binder. -/
theorem receiver_subst (b : Name) :
    PiCalculus.subst (receiverWorker (.var 0)) b = receiverWorker b := rfl

/-- **Pending state steps by invoking the sender trigger.**
The first real trigger Step, leaving both persistent daemons untouched. -/
theorem sender_invocation (b : Name) : PiCalculus.Step (pending b) (sentInvoked b) := by
  exact PiCalculus.Step.parL (service_invocation_step 710 b (senderWorker (.var 0)))

/-- **Sender-invoked state steps by invoking the receiver trigger.**
The second actual trigger Step, not a pre-generated finite unrolling. -/
theorem receiver_invocation (b : Name) : PiCalculus.Step (sentInvoked b) (bothInvoked b) := by
  exact PiCalculus.Step.parR (service_invocation_step 711 b (receiverWorker (.var 0)))

/-- **Interchange law for four parallel components.**
Four canonical parallel components regroup without evaluating any body. -/
theorem parallel_interchange (a b c d : Proc) :
    Cong (.par (.par a b) (.par c d)) (.par (.par a c) (.par b d)) := by
  apply Cong.trans (Cong.par_assoc a b (.par c d))
  apply Cong.trans (Cong.par_cong (Cong.refl a) (Cong.symm (Cong.par_assoc b c d)))
  apply Cong.trans (Cong.par_cong (Cong.refl a) (Cong.par_cong (Cong.par_comm b c) (Cong.refl d)))
  exact Cong.trans (Cong.par_cong (Cong.refl a) (Cong.par_assoc c b d))
    (Cong.symm (Cong.par_assoc a c (.par b d)))

/-- **Data substitution yields the receiver's return request.**
A passive input removes ONLY its data binder, retaining the actual endpoint. -/
theorem receiver_return_subst (b : Name) :
    PiCalculus.subst (.out (.const 711) (liftName 0 b) .nil) (.const 712) = receiverRequest b := by
  change Proc.out (.const 711) (substName (.const 712) 0 (liftName 0 b)) .nil = _
  rw [substName_liftName]
  rfl

/-- **Session action steps back to the pending state.**
Actual session action restores BOTH pending endpoint-role transfers and daemons. -/
theorem session_and_reentry (b : Name) : PiCalculus.Step (bothInvoked b) (pending b) := by
  have hs : PiCalculus.Step (.par (senderWorker b) (receiverWorker b))
      (.par (senderRequest b) (receiverRequest b)) := by
    have ht := PiCalculus.Step.commSelect
      (Select.refl (senderWorker b)) (Select.refl (receiverWorker b))
    rw [receiver_return_subst] at ht
    exact ht
  exact PiCalculus.Step.cong (parallel_interchange _ _ _ _) (PiCalculus.Step.parL hs)
    (Cong.symm (parallel_interchange _ _ _ _))

end Cslib.SessionTypes.Endpoint.Runtime
