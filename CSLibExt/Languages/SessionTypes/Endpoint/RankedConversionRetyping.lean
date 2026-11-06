/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextEquivalence

/-! # Actual equivalent-context preservation of every static guard -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- **Equivalent contexts preserve the guard condition.**
Same domains, literal cap ranks and actual done equivalence preserve GuardMin. -/
theorem GuardMin.retype {Δ Ξ : Context} {e : Key} {k : Nat} (hg : GuardMin Δ e k)
    (he : ContextEquivalent Δ Ξ) : GuardMin Ξ e k := by
  intro d c hc ha hd
  obtain ⟨v, hv, hr⟩ := he.symm.lookup hc
  have hvactive : v.protocol.unfold ≠ .done := fun hdone => ha (hr.2.done_iff.mpr hdone)
  rw [hr.1]
  exact hg d v hv hvactive hd

namespace Conversion

open PiCalculus

/-- **Equivalent contexts preserve conversion ranked typing.**
GENERAL arbitrary-depth, arbitrary-context retyping, by all seven typing
constructors. Target ownership, ranks and every unfolded branch are derived. -/
theorem RankedType.retype {n : Nat} {Δ Ξ : Context} {p : Proc}
    (h : RankedType n Δ p) (he : ContextEquivalent Δ Ξ) : RankedType n Ξ p := by
  induction h generalizing Ξ with
  | nil hc hs => exact RankedType.nil (he.completed hc) (he.scope hs)
  | @outName n Δ e c b s p hg hc hh ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | sendName hs =>
      exact RankedType.outName (by rw [← hr.1]; exact hg.retype he) hc' hu ha hb
        (ih (he.insert e ⟨hr.1, hs⟩))
  | @inpName n Δ e c s p hg hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvName _ t hs =>
      exact RankedType.inpName (by rw [← hr.1]; exact hg.retype he) hc' hu ha
        (ih ((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, t⟩) ⟨hr.1, hs⟩).lift 0))
  | @outEndpoint n Δ e d c v k t s p hg hc hh hv hvt hne ha hb hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    obtain ⟨v', hv', hrv⟩ := he.lookup hv
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @sendEndpoint _ _ _ t' _ s' ht hs =>
      have hpayload : (⟨k, t⟩ : Capability).Equivalent ⟨k, t'⟩ := ⟨rfl, ht⟩
      have hvnew := (hrv.symm.trans hvt).trans hpayload
      exact RankedType.outEndpoint (by rw [← hr.1]; exact hg.retype he) hc' hu hv' hvnew hne ha hb
        (ih ((he.erase d).insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩))
  | @inpEndpoint n Δ e c r k t s p hg hc hh ha hp ih =>
    obtain ⟨c', hc', hr⟩ := he.lookup hc
    have hm := hr.2.head
    rw [hh] at hm
    generalize hu : c'.protocol.unfold = u at hm
    cases hm with
    | @recvEndpoint _ _ _ t' _ s' ht hs =>
      exact RankedType.inpEndpoint (by rw [← hr.1]; exact hg.retype he) hc' hu ha
        (ih (((he.insert e (c := ⟨c.rank, s⟩) (d := ⟨c'.rank, s'⟩) ⟨hr.1, hs⟩).lift 0).insert
          ⟨.var 0, r⟩ (c := ⟨k, t⟩) (d := ⟨k, t'⟩) ⟨rfl, ht⟩))
  | par hd hp hq ihp ihq =>
    obtain ⟨Γ', Θ', hwhole, hd', hΓ, hΘ⟩ := he.split hd
    rw [hwhole]
    exact RankedType.par hd' (ihp hΓ) (ihq hΘ)
  | @nu n Δ c p hp ih =>
    exact RankedType.nu (c := c) (ih (he.bind (Capability.Equivalent.refl c)))

/-- **Context equivalence transports conversion ranked typing both ways.**
Equivalence transports typing in BOTH directions at the same process/depth. -/
theorem RankedType.retype_iff {n : Nat} {Δ Ξ : Context} {p : Proc}
    (he : ContextEquivalent Δ Ξ) : RankedType n Δ p ↔ RankedType n Ξ p :=
  ⟨fun h => h.retype he, fun h => h.retype he.symm⟩


end Conversion
end Cslib.SessionTypes.Endpoint
