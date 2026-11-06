/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeNormalization
public import CSLibExt.Languages.SessionTypes.Endpoint.ServiceExposure
public import CSLibExt.Languages.SessionTypes.Endpoint.PersistentOffers

/-!
# Exposed shared requests fire from actual persistent availability

This case precedes active-key reasoning: a request may transfer a DONE capability.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Non-request-free frontier exposes a shared output up to congruence.**
A non-request-free frontier yields an ACTUAL declared output leaf through
canonical par rearrangement. Neither readiness nor a progress result is supplied. -/
theorem GuardedFrontier.expose_request {Γ : ServiceEnv} {p : Proc} (hf : GuardedFrontier Γ p)
    (hn : ¬ RequestFree Γ p) :
    ∃ s sig b c r, Γ.lookup s = some sig ∧ Cong p (.par (.out (.const s) b c) r) := by
  classical
  induction hf with
  | template ht => exact False.elim (hn ht.request_free)
  | out a b c =>
    change ¬ (∀ s sig, Γ.lookup s = some sig → a ≠ .const s) at hn
    push Not at hn
    obtain ⟨s, sig, hs, ha⟩ := hn
    subst a
    exact ⟨s, sig, b, c, .nil, hs, (Cong.par_nil _).symm⟩
  | inp => exact False.elim (hn trivial)
  | @par p q hp hq ihp ihq =>
    by_cases hf : RequestFree Γ p
    · have hnq : ¬ RequestFree Γ q := fun hq => hn ⟨hf, hq⟩
      obtain ⟨s, sig, b, c, r, hs, hc⟩ := ihq hnq
      exact ⟨s, sig, b, c, .par r p, hs,
        Cong.trans (Cong.par_cong (Cong.refl p) hc)
          (Cong.trans (Cong.par_comm p _) (Cong.par_assoc _ _ _))⟩
    · obtain ⟨s, sig, b, c, r, hs, hc⟩ := ihp hf
      exact ⟨s, sig, b, c, .par r q, hs,
        Cong.trans (Cong.par_cong hc (Cong.refl q)) (Cong.par_assoc _ _ _)⟩

/-- **Exposed shared requests step when declared services are available.**
Any actual exposed request fires under the EXISTING all-declared-services
availability qualifier, even with ZERO active owned keys or a DONE payload.
The Step is constructed from actual offered input syntax, not stored in Available. -/
theorem GuardedFrontier.request_progress {Γ : ServiceEnv} {p : Proc} (hf : GuardedFrontier Γ p)
    (hn : ¬ RequestFree Γ p) (ha : Available Γ p) : ∃ q, PiCalculus.Step p q := by
  obtain ⟨s, sig, b, c, r, hs, hc⟩ := hf.expose_request hn
  have hav := (Available.cong_iff hc).mp ha
  have ho : OfferedIn s r := (hav s sig hs).elim False.elim id
  obtain ⟨q, hstep⟩ := offered_invocation_step ho b c
  exact ⟨q, PiCalculus.Step.cong hc hstep (Cong.refl _)⟩

end Cslib.SessionTypes.Endpoint.Runtime
