/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionTransport
public import CSLibExt.Languages.SessionTypes.Endpoint.Substitution

/-!
# Canonical substitution of actual linear capabilities in conversion typing

The advertised input capability can differ as code from the actual owned
payload. Only its received slot is retyped before capture-safe name transport.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Endpoint substitution preserves conversion typing.**
GENERAL endpoint substitution: retain the ACTUAL transmitted capability's
code and rank at the sent polarized key, allowing its opposite-role alias.
Collision freedom is needed only for that exact key and canonical substitution. -/
theorem HasType.subst_endpoint {n : Nat} {Δ : Context} {b : Name} {r : Role}
    {c v : Capability} {p : Proc}
    (h : HasType (n + 1) ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) p)
    (he : v.Equivalent c) (hb : b.ClosedAt n) (hfresh : (⟨b, r⟩ : Key) ∉ Δ) :
    HasType n (Δ.insert ⟨b, r⟩ v) (PiCalculus.subst p b) := by
  have ht := h.retype ((ContextEquivalent.refl (Context.lift 0 Δ)).insert ⟨.var 0, r⟩ he.symm)
  have hi := Context.injOn_received_subst (c := v) hfresh
  have hr := ht.rename (fun _ ha => hb.subst ha (Nat.zero_le n)) hi
  rw [Context.rekey_received_subst hfresh hi, mapProc_substName] at hr
  exact hr

/-- **Endpoint substitution with freshness from a disjoint split.**
GENERAL split-derived freshness: actual payload ownership and the
receiver's already-owned carrier derive non-aliasing even after advancement. -/
theorem HasType.subst_endpoint_from_split {n : Nat} {Γ Θ : Context} {b : Name} {r : Role}
    {c v old next : Capability} {e : Key} {p : Proc}
    (hd : Finmap.Disjoint Γ Θ) (hv : Γ.lookup ⟨b, r⟩ = some v)
    (hc : Θ.lookup e = some old)
    (h : HasType (n + 1) ((Context.lift 0 (Θ.insert e next)).insert ⟨.var 0, r⟩ c) p)
    (he : v.Equivalent c) (hb : b.ClosedAt n) :
    HasType n ((Θ.insert e next).insert ⟨b, r⟩ v) (PiCalculus.subst p b) := by
  apply h.subst_endpoint he hb
  exact Context.fresh_insert_owned (Context.fresh_of_disjoint hd hv)
    (Finmap.mem_of_lookup_eq_some hc)

/-- **Passive name substitution preserves conversion typing.**
GENERAL passive substitution transports all scoped positions but adds
NO capability. The input context contains only lifted outer ownership. -/
theorem HasType.subst_passive {n : Nat} {Δ : Context} {p : Proc} {b : Name}
    (h : HasType (n + 1) (Context.lift 0 Δ) p) (hb : b.ClosedAt n) :
    HasType n Δ (PiCalculus.subst p b) := by
  have hi := Context.injOn_passive_subst (Δ := Δ) b
  have ht := h.rename (fun _ ha => hb.subst ha (Nat.zero_le n)) hi
  rw [Context.rekey_passive_subst b hi, mapProc_substName] at ht
  exact ht

end Cslib.SessionTypes.Endpoint.Conversion
