/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeTransport
public import CSLibExt.Languages.SessionTypes.Endpoint.Substitution

/-!
# Actual endpoint and passive substitution with shared-name nonalias

Linear input retains the actual transmitted cap's code/rank/role. Passive
input has no owned var0 and may receive a shared constant without acquiring
its linear ownership. All transformations are the canonical Pi substitution.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Nonshared endpoint substitution keeps owned names nonshared.**
An actual nonshared endpoint replacement keeps every owned substituted image nonshared. -/
theorem Separated.nonaliases_subst {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ)
    {b : Name} (hb : ∀ s sig, Γ.lookup s = some sig → b ≠ .const s) :
    NonAliases Γ Δ (substName b 0) := by
  rintro ⟨a, r⟩ hm s sig hs hn
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp hm
  cases a with
  | const k => exact h _ c hc s sig hs hn
  | var i =>
    cases i with
    | zero => exact hb s sig hs hn
    | succ i => simp [substName] at hn

/-- **Passive substitution creates no owned shared-name alias.**
Passive var0 is NOT owned: even a shared-constant replacement preserves all
actual lifted owned names and creates no linear shared-name alias. -/
theorem Separated.nonaliases_passive {Γ : ServiceEnv} {Δ : Context}
    (h : Separated Γ (Context.lift 0 Δ)) (b : Name) :
    NonAliases Γ (Context.lift 0 Δ) (substName b 0) := by
  rintro ⟨a, r⟩ hm s sig hs hn
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp hm
  cases a with
  | const k => exact h _ c hc s sig hs hn
  | var i =>
    cases i with
    | zero => exact False.elim (Context.fresh_lift Δ r hm)
    | succ i => simp [substName] at hn

/-- **Runtime typing under substitution of a transmitted endpoint.**
Actual transmitted endpoint substitution preserves literal role/rank and raw code.
Shared nonalias of b is a static consequence of ACTUAL sender ownership/separation. -/
theorem HasType.subst_endpoint {n : Nat} {Γ : ServiceEnv} {Δ : Context} {b : Name} {r : Role}
    {c v : Capability} {p : Proc}
    (h : HasType (n + 1) Γ ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) p)
    (he : v.Equivalent c) (hb : b.ClosedAt n) (hfresh : (⟨b, r⟩ : Key) ∉ Δ)
    (hshared : ∀ s sig, Γ.lookup s = some sig → b ≠ .const s) :
    HasType n Γ (Δ.insert ⟨b, r⟩ v) (PiCalculus.subst p b) := by
  have ht := h.retype ((ContextEquivalent.refl (Context.lift 0 Δ)).insert ⟨.var 0, r⟩ he.symm)
  have hi := Context.injOn_received_subst (c := v) hfresh
  have hr := ht.rename (fun _ ha => hb.subst ha (Nat.zero_le n))
    (fun _ _ _ => rfl) (ht.separated.nonaliases_subst hshared) hi
  rw [Context.rekey_received_subst hfresh hi, mapProc_substName] at hr
  exact hr

/-- **Runtime typing under passive name substitution.**
Passive substitution has NO owned var0 and adds NO capability. A scoped shared
constant can be received as data without becoming a linear/service subject. -/
theorem HasType.subst_passive {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc} {b : Name}
    (h : HasType (n + 1) Γ (Context.lift 0 Δ) p) (hb : b.ClosedAt n) :
    HasType n Γ Δ (PiCalculus.subst p b) := by
  have hi := Context.injOn_passive_subst (Δ := Δ) b
  have ht := h.rename (fun _ ha => hb.subst ha (Nat.zero_le n))
    (fun _ _ _ => rfl) (h.separated.nonaliases_passive b) hi
  rw [Context.rekey_passive_subst b hi, mapProc_substName] at ht
  exact ht

/-- **Endpoint substitution with side conditions derived from a split.**
Real sender ownership and a disjoint receiver carrier derive exact-role
freshness and shared nonalias of the actual transmitted endpoint. -/
theorem HasType.subst_endpoint_from_split {n : Nat} {Γ : ServiceEnv} {Λ Θ : Context}
    {b : Name} {r : Role} {c v old next : Capability} {e : Key} {p : Proc}
    (hsep : Separated Γ Λ) (hd : Finmap.Disjoint Λ Θ) (hv : Λ.lookup ⟨b, r⟩ = some v)
    (hc : Θ.lookup e = some old)
    (h : HasType (n + 1) Γ ((Context.lift 0 (Θ.insert e next)).insert ⟨.var 0, r⟩ c) p)
    (he : v.Equivalent c) (hb : b.ClosedAt n) :
    HasType n Γ ((Θ.insert e next).insert ⟨b, r⟩ v) (PiCalculus.subst p b) := by
  apply h.subst_endpoint he hb
  · exact Context.fresh_insert_owned (Context.fresh_of_disjoint hd hv)
      (Finmap.mem_of_lookup_eq_some hc)
  · exact hsep ⟨b, r⟩ v hv

end Cslib.SessionTypes.Endpoint.Runtime
