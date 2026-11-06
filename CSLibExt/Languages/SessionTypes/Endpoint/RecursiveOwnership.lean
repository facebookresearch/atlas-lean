/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveTrigger
public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeInversion

/-!
# Concrete ownership-consistent recursive trigger invocation and reset

Each service receives exactly one endpoint role. The fixed regular protocol
advances to itself, with no fresh session or duplicated captured capability.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Sender service signature of the recurring example.**
Static sender and receiver permissions use opposite roles, exact rank7 types. -/
def senderSignature (r : Role) : ServiceSignature := ⟨0, r, recurringCap⟩

/-- **Receiver service signature of the recurring example.**
Opposite-role receive permission retains the exact literal dual capability. -/
def receiverSignature (r : Role) : ServiceSignature := ⟨0, r.opposite, recurringCap.dual⟩

/-- **Service environment declaring the two triggers.**
Two distinct declared constant triggers; declaration alone is not an offer. -/
def services (r : Role) : ServiceEnv := (Finmap.singleton 710 (senderSignature r)).insert
  711 (receiverSignature r)

/-- **Endpoint distinct from both service triggers.**
Session endpoints are physically distinct from BOTH declared shared triggers. -/
def EndpointFresh (b : Name) : Prop := b ≠ .const 710 ∧ b ≠ .const 711

/-- **The sender trigger declares the sender signature.**
Actual sender signature lookup with literal role, cap rank and raw protocol. -/
theorem sender_declared (r : Role) : (services r).lookup 710 = some (senderSignature r) := by
  rw [services, Finmap.lookup_insert_of_ne _ (by decide : (710 : Nat) ≠ 711),
    Finmap.lookup_singleton_eq]

/-- **The receiver trigger declares the receiver signature.**
The other trigger declares exactly the opposite-role receive permission. -/
theorem receiver_declared (r : Role) : (services r).lookup 711 = some (receiverSignature r) :=
  Finmap.lookup_insert _

/-- **Lifting preserves trigger freshness of an endpoint.**
Actual canonical lifting cannot turn a distinct endpoint into a service constant. -/
theorem EndpointFresh.lift {b : Name} (h : EndpointFresh b) : EndpointFresh (liftName 0 b) := by
  cases b with
  | const => exact h
  | var i => constructor <;> intro he <;> cases he

/-- **A fresh endpoint singleton is separated from the triggers.**
The exact actual-role singleton does not capture a shared trigger as a linear name. -/
theorem endpoint_separated (r role : Role) (b : Name) (c : Capability) (hb : EndpointFresh b) :
    Separated (services r) (Finmap.singleton (⟨b, role⟩ : Key) c) := by
  apply separated_singleton
  intro s sig hs
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hs) with he | he
  · subst s
    exact hb.2
  · have he := (Finmap.mem_singleton _ _ _).mp he
    subst s
    exact hb.1

/-- **Erasing a singleton's only key leaves the empty map.**
Erasing the actual sole endpoint leaves exactly the empty ownership map.
Shared by request and delegation consumers instead of duplicating lookup proofs. -/
theorem erase_singleton (e : Key) (c : Capability) :
    (Finmap.singleton e c : Context).erase e = ∅ := by
  apply Finmap.ext_lookup
  intro x
  by_cases he : x = e
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_empty]
  · rw [Finmap.lookup_erase_ne he, Finmap.lookup_eq_none.mpr (by simpa using he),
      Finmap.lookup_empty]

/-- **Nil is runtime-typed with empty ownership.**
Nil embeds the finite ranked fragment with genuinely empty ownership. -/
theorem nil_typed (n : Nat) (Γ : ServiceEnv) : HasType n Γ ∅ .nil :=
  HasType.of_finite (Conversion.RankedType.nil Context.completed_empty
    (fun _ hx => False.elim (Finmap.notMem_empty hx))) (separated_empty Γ)

/-- **The sender reentry request is runtime-typed.**
Reentry transfers the actual sender capability out, preserving role/rank/code. -/
theorem sender_request_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r)
    (Finmap.singleton (⟨b, r⟩ : Key) recurringCap) (senderRequest b) := by
  apply HasType.invoke (s := 710) (sig := senderSignature r) (e := ⟨b, r⟩) (v := recurringCap)
    (sender_declared r) (endpoint_separated r r b recurringCap hf)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Capability.Equivalent.refl _
  · exact invocation_priority_singleton _ _ _ (by decide : 0 < 7)
  · exact hb
  · rw [erase_singleton]
    exact nil_typed n _

/-- **The receiver reentry request is runtime-typed.**
Reentry of the opposite role likewise consumes EXACTLY its own linear slot. -/
theorem receiver_request_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r)
    (Finmap.singleton (⟨b, r.opposite⟩ : Key) recurringCap.dual) (receiverRequest b) := by
  apply HasType.invoke (s := 711) (sig := receiverSignature r) (e := ⟨b, r.opposite⟩)
    (v := recurringCap.dual) (receiver_declared r)
    (endpoint_separated r r.opposite b recurringCap.dual hf)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Capability.Equivalent.refl _
  · exact invocation_priority_singleton _ _ _ (by decide : 0 < 7)
  · exact hb
  · rw [erase_singleton]
    exact nil_typed n _

/-- **The sender worker is runtime-typed.**
One linear session send keeps the same actual guarded protocol cursor and rank. -/
theorem sender_worker_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r)
    (Finmap.singleton (⟨b, r⟩ : Key) recurringCap) (senderWorker b) := by
  apply HasType.outName (e := ⟨b, r⟩) (c := recurringCap) (s := recurringProtocol)
    (guardMin_singleton _ _) (endpoint_separated r r b recurringCap hf)
  · exact Finmap.lookup_singleton_eq
  · exact recurring_unfold
  · exact hb
  · trivial
  · rw [Finmap.insert_singleton_eq]
    exact sender_request_typed r b hb hf

/-- **The receiver worker is runtime-typed.**
One receive retains the outer received endpoint through its passive input binder. -/
theorem receiver_worker_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r)
    (Finmap.singleton (⟨b, r.opposite⟩ : Key) recurringCap.dual) (receiverWorker b) := by
  apply HasType.inpName (e := ⟨b, r.opposite⟩) (c := recurringCap.dual)
    (s := recurringProtocol.dual) (guardMin_singleton _ _)
    (endpoint_separated r r.opposite b recurringCap.dual hf)
  · exact Finmap.lookup_singleton_eq
  · exact recurring_dual_unfold
  · exact hb
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact receiver_request_typed r (liftName 0 b) hb.lift hf.lift

/-- **The sender daemon is typed with empty ownership.**
The sender daemon starts with NO captured linear capability, only its fresh formal. -/
theorem sender_daemon_typed (n : Nat) (r : Role) : HasType n (services r) ∅ senderDaemon :=
  HasType.serve_input (sender_declared r)
    (sender_worker_typed r (.var 0) (Nat.zero_lt_succ n)
      (by constructor <;> intro h <;> cases h))
    Context.completed_empty (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty _)

/-- **The receiver daemon is typed with empty ownership.**
The receiver daemon likewise captures no linear endpoint, in either orientation. -/
theorem receiver_daemon_typed (n : Nat) (r : Role) : HasType n (services r) ∅ receiverDaemon :=
  HasType.serve_input (receiver_declared r)
    (receiver_worker_typed r (.var 0) (Nat.zero_lt_succ n)
      (by constructor <;> intro h <;> cases h))
    Context.completed_empty (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty _)

/-- **Two-role linear interface of the recurring session.**
Actual linear interface, one sender role and its opposite receiver role. -/
def recurringInterface (b : Name) (r : Role) : Context :=
  Finmap.singleton ⟨b, r⟩ recurringCap ∪ Finmap.singleton ⟨b, r.opposite⟩ recurringCap.dual

private theorem opposite_disjoint (b : Name) (r : Role) : Finmap.Disjoint
    (Finmap.singleton (⟨b, r⟩ : Key) recurringCap : Context)
    (Finmap.singleton (⟨b, r.opposite⟩ : Key) recurringCap.dual) := by
  cases r <;> simp [Finmap.Disjoint, Finmap.mem_singleton, Role.opposite]

private theorem frame_empty {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (hp : HasType n Γ Δ p) (hq : HasType n Γ ∅ q) : HasType n Γ Δ (.par p q) := by
  have h : HasType n Γ (Δ ∪ ∅) (.par p q) :=
    HasType.par (fun _ _ he => Finmap.notMem_empty he) hp hq
  simpa using h

private theorem frame_workers {n : Nat} {b : Name} {r : Role} {p q : Proc}
    (hp : HasType n (services r) (Finmap.singleton (⟨b, r⟩ : Key) recurringCap) p)
    (hq : HasType n (services r) (Finmap.singleton (⟨b, r.opposite⟩ : Key) recurringCap.dual) q) :
    HasType n (services r) (recurringInterface b r)
      (.par (.par p senderDaemon) (.par q receiverDaemon)) :=
  HasType.par (opposite_disjoint b r) (frame_empty hp (sender_daemon_typed n r))
    (frame_empty hq (receiver_daemon_typed n r))

/-- **The pending state is typed at the two-role interface.**
The real pending state owns two distinct opposite keys, not daemon captures. -/
theorem pending_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r) (recurringInterface b r) (pending b) :=
  frame_workers (sender_request_typed r b hb hf) (receiver_request_typed r b hb hf)

/-- **The state after the sender invocation is typed.**
First invocation transfers the exact sender slot into one worker; frame unchanged. -/
theorem sentInvoked_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r) (recurringInterface b r) (sentInvoked b) :=
  frame_workers (sender_worker_typed r b hb hf) (receiver_request_typed r b hb hf)

/-- **The state after both trigger invocations is typed.**
Both workers own their actual distinct roles after the two trigger communications. -/
theorem bothInvoked_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) : HasType n (services r) (recurringInterface b r) (bothInvoked b) :=
  frame_workers (sender_worker_typed r b hb hf) (receiver_worker_typed r b hb hf)

end Cslib.SessionTypes.Endpoint.Runtime
