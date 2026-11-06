/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextEquivalence

/-!
# Arbitrary-context semantic retyping of the seven-rule conversion judgement

Actual target heads and finite ownership splits are derived from pointwise
rank/tree equivalence. No consistent representative, ready edge, matching
split or retyping proof is an admission field.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Retyping along ownership-map equivalence.**
GENERAL arbitrary-depth, arbitrary-context retyping, by all seven typing
constructors. Target ownership, ranks and every unfolded branch are derived. -/
theorem HasType.retype {n : Nat} {Δ Ξ : Context} {p : Proc}
    (h : HasType n Δ p) (he : ContextEquivalent Δ Ξ) : HasType n Ξ p := by
  induction h generalizing Ξ with
  | nil hc hs => exact HasType.nil (he.completed hc) (he.scope hs)
  | @outName n Δ e c b s p hc hh ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | sendName hs =>
      exact HasType.outName hc' hu ha hb (ih (he.insert e ⟨hr.1, hs⟩))
  | @inpName n Δ e c s p hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvName _ t hs =>
      exact HasType.inpName hc' hu ha
        (ih ((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, t⟩) ⟨hr.1, hs⟩).lift 0))
  | @outEndpoint n Δ e d c v k t s p hc hh hv hvt hne ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    obtain ⟨v', hv', hrv⟩ := he.lookup hv
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @sendEndpoint _ _ _ t' _ s' ht hs =>
      have hpayload : (⟨k, t⟩ : Capability).Equivalent ⟨k, t'⟩ := ⟨rfl, ht⟩
      have hvnew := (hrv.symm.trans hvt).trans hpayload
      exact HasType.outEndpoint hc' hu hv' hvnew hne ha hb
        (ih ((he.erase d).insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩))
  | @inpEndpoint n Δ e c r k t s p hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvEndpoint _ _ _ t' _ s' ht hs =>
      exact HasType.inpEndpoint hc' hu ha
        (ih (((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩).lift 0).insert
          ⟨.var 0, r⟩ (c := ⟨k, t⟩) (d := ⟨k, t'⟩) ⟨rfl, ht⟩))
  | par hd hp hq ihp ihq =>
    obtain ⟨Γ', Θ', hwhole, hd', hΓ, hΘ⟩ := he.split hd
    rw [hwhole]
    exact HasType.par hd' (ihp hΓ) (ihq hΘ)
  | @nu n Δ c p hp ih =>
    exact HasType.nu (c := c) (ih (he.bind (Capability.Equivalent.refl c)))

/-- **Ownership-map equivalence preserves typing in both directions.**
Equivalence transports typing in BOTH directions at the same process/depth. -/
theorem HasType.retype_iff {n : Nat} {Δ Ξ : Context} {p : Proc}
    (he : ContextEquivalent Δ Ξ) : HasType n Δ p ↔ HasType n Ξ p :=
  ⟨fun h => h.retype he, fun h => h.retype he.symm⟩

end Cslib.SessionTypes.Endpoint.Conversion
