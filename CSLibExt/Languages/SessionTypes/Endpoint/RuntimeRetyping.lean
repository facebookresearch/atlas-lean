/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeInversion
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionRetyping

/-!
# Arbitrary-context runtime retyping at unchanged shared permissions

Literal domains/ranks and actual active/done observations are derived from
ContextEquivalent. Replicated BODY ownership stays EMPTY independently of its
completed ambient annotations. No representative/result admission is used.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Semantic capability changes do not change owned physical names or Γ separation. -/
theorem Separated.retype {Γ : ServiceEnv} {Δ Ξ : Context} (hs : Separated Γ Δ)
    (he : ContextEquivalent Δ Ξ) : Separated Γ Ξ := by
  intro e c hc s sig hsig
  obtain ⟨v, hv, hr⟩ := he.symm.lookup hc
  exact hs e v hv s sig hsig

/-- Actual active-payload ranks preserve the strict shared invocation priority. -/
theorem InvocationPriority.retype {sig : ServiceSignature} {Δ Ξ : Context}
    (hg : InvocationPriority sig Δ) (he : ContextEquivalent Δ Ξ) : InvocationPriority sig Ξ := by
  intro e c hc ha
  obtain ⟨v, hv, hr⟩ := he.symm.lookup hc
  have hva : v.protocol.unfold ≠ .done := fun hd => ha (hr.2.done_iff.mpr hd)
  rw [hr.1]
  exact hg e v hv hva

/-- ALL10 runtime rules retype at arbitrary equivalent linear contexts, with Γ
UNCHANGED. Actual payload codes, literal cap ranks and empty BODY contexts are retained. -/
theorem HasType.retype {n : Nat} {Γ : ServiceEnv} {Δ Ξ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (he : ContextEquivalent Δ Ξ) : HasType n Γ Ξ p := by
  induction h generalizing Ξ with
  | nil hc hscope hs => exact HasType.nil (he.completed hc) (he.scope hscope) (hs.retype he)
  | @outName n Γ Δ e c b s p hg hsep hc hh ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | sendName hs =>
      exact HasType.outName (hr.1 ▸ hg.retype he) (hsep.retype he) hc' hu ha hb
        (ih (he.insert e ⟨hr.1, hs⟩))
  | @inpName n Γ Δ e c s p hg hsep hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvName _ t hs =>
      exact HasType.inpName (hr.1 ▸ hg.retype he) (hsep.retype he) hc' hu ha
        (ih ((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, t⟩) ⟨hr.1, hs⟩).lift 0))
  | @outEndpoint n Γ Δ e d c v k t s p hg hsep hc hh hv hvt hne ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    obtain ⟨v', hv', hrv⟩ := he.lookup hv
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @sendEndpoint _ _ _ t' _ s' ht hs =>
      have hpayload : (⟨k, t⟩ : Capability).Equivalent ⟨k, t'⟩ := ⟨rfl, ht⟩
      have hvnew := (hrv.symm.trans hvt).trans hpayload
      exact HasType.outEndpoint (hr.1 ▸ hg.retype he) (hsep.retype he) hc' hu hv' hvnew hne ha hb
        (ih ((he.erase d).insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩))
  | @inpEndpoint n Γ Δ e c r k t s p hg hsep hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvEndpoint _ _ _ t' _ s' ht hs =>
      exact HasType.inpEndpoint (hr.1 ▸ hg.retype he) (hsep.retype he) hc' hu ha
        (ih (((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩).lift 0).insert
          ⟨.var 0, r⟩ (c := ⟨k, t⟩) (d := ⟨k, t'⟩) ⟨rfl, ht⟩))
  | @invoke n Γ Δ s sig e v p hs hsep hv hr hve hg hb hp ih =>
    obtain ⟨v', hv', hvv⟩ := he.lookup hv
    exact HasType.invoke hs (hsep.retype he) hv' hr (hvv.symm.trans hve) (hg.retype he) hb
      (ih (he.erase e))
  | accept hs hc hscope hsep hp ih =>
    exact HasType.accept hs (he.completed hc) (he.scope hscope) (hsep.retype he) hp
  | serve ht hp hc hscope hsep ih =>
    exact HasType.serve ht hp (he.completed hc) (he.scope hscope) (hsep.retype he)
  | par hd hp hq ihp ihq =>
    obtain ⟨Δ', Θ', hwhole, hd', hΔ, hΘ⟩ := he.split hd
    rw [hwhole]
    exact HasType.par hd' (ihp hΔ) (ihq hΘ)
  | @nu n Γ Δ c p hs hp ih =>
    exact HasType.nu (hs.retype he) (ih (he.bind (Capability.Equivalent.refl c)))

/-- Equivalent linear interfaces preserve runtime typing in BOTH directions at
exactly the same shared environment, process and ambient depth. -/
theorem HasType.retype_iff {n : Nat} {Γ : ServiceEnv} {Δ Ξ : Context} {p : Proc}
    (he : ContextEquivalent Δ Ξ) : HasType n Γ Δ p ↔ HasType n Γ Ξ p :=
  ⟨fun h => h.retype he, fun h => h.retype he.symm⟩

end Cslib.SessionTypes.Endpoint.Runtime
