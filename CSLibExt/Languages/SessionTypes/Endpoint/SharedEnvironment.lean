/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Context

/-!
# Separate classical shared permissions and linear-name separation

Signatures carry static endpoint observations, not linear ownership or
execution/typing results. Constants are the conservative shared-name fragment.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Shared service signature.**
Shared permission describes a transferred endpoint, not owned linear state. -/
structure ServiceSignature where
  priority : Nat
  role : Role
  capability : Capability

/-- **Shared service environment.**
Constant-only shared names use the existing Finmap, not a new name foundation. -/
abbrev ServiceEnv := Finmap (fun _ : Nat => ServiceSignature)

/-- **Separation of owned linear names from shared names.**
An owned linear endpoint is never a declared shared trigger's physical name. -/
def Separated (Γ : ServiceEnv) (Δ : Context) : Prop :=
  ∀ e c, Δ.lookup e = some c → ∀ s sig, Γ.lookup s = some sig → e.name ≠ .const s

/-- **Priority of a shared invocation over active owned keys.**
Shared invocation precedes every actual active owned LINEAR key; none exempt. -/
def InvocationPriority (sig : ServiceSignature) (Δ : Context) : Prop :=
  ∀ e c, Δ.lookup e = some c → c.protocol.unfold ≠ .done → sig.priority < c.rank

/-- **Empty ownership is separated from shared names.**
Empty captured ownership has no linear/shared alias. -/
theorem separated_empty (Γ : ServiceEnv) : Separated Γ ∅ := by
  intro e c hc
  simp at hc

/-- **Singleton context with a nonshared name is separated.**
A singleton received/actual endpoint is separate exactly at its own name. -/
theorem separated_singleton {Γ : ServiceEnv} {e : Key} {c : Capability}
    (he : ∀ s sig, Γ.lookup s = some sig → e.name ≠ .const s) :
    Separated Γ (Finmap.singleton e c) := by
  intro x v hv s sig hs
  have hx := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst x
  exact he s sig hs

/-- **Invocation priority for a singleton of rank above the priority.**
Singleton invocation still compares the ACTIVE payload's actual cap rank. -/
theorem invocation_priority_singleton (sig : ServiceSignature) (e : Key) (c : Capability)
    (hr : sig.priority < c.rank) : InvocationPriority sig (Finmap.singleton e c) := by
  intro x v hv ha
  have hx := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
  subst x
  rw [Finmap.lookup_singleton_eq] at hv
  cases hv
  exact hr

end Cslib.SessionTypes.Endpoint.Runtime
