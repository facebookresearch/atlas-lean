/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeLinearProgress
public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeRequests
public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeReduction

/-!
# Internally derived guarded runtime frontier progress

Actual requests (including DONE payloads) precede the all-active-owned-key minimum.
The only availability qualification is the existing all-declared-services predicate.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Balanced runtime frontiers are idle or step given availability.**
A typed balanced runtime frontier with actual persistent service availability
is syntactically Idle OR takes an ACTUAL canonical Step. Shared requests are
handled even if all owned keys are done; minimum/peer leaves are derived internally. -/
theorem GuardedFrontier.progress {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (hf : GuardedFrontier Γ p) (ht : HasType n Γ Δ p) (hb : Conversion.Balanced Δ)
    (hav : Available Γ p) : Idle Γ p ∨ ∃ q, PiCalculus.Step p q := by
  classical
  by_cases hreq : RequestFree Γ p
  · by_cases hactive : ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done
    · obtain ⟨e, c, he, ha, hmin⟩ := Context.active_minimum hactive
      obtain ⟨Λ, Θ, g, r, rfl, hd, heg, hcg, htg, htr, hshape, hfr⟩ :=
        hf.expose_minimum ht hreq he ha hmin
      have hfree := (RequestFree.cong_iff hcg).mp hreq
      obtain ⟨d, hep, hdual⟩ := hb e c he
      have hminΛ : ∀ x v, Λ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank :=
        fun x v hx hv => hmin x v
          ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)).trans hx) hv
      have hnot : e.opposite ∉ Λ := by
        intro hem
        rw [Finmap.lookup_union_left hem] at hep
        exact minimum_peer_separate htg hfree.1 heg ha hminΛ hshape hdual hep
      have heΘ : Θ.lookup e.opposite = some d := by
        rw [Finmap.lookup_union_right hnot] at hep
        exact hep
      have hminΘ : ∀ x v, Θ.lookup x = some v → v.protocol.unfold ≠ .done → d.rank ≤ v.rank := by
        intro x v hx hv
        rw [hdual.1]
        exact hmin x v ((Finmap.lookup_union_right
          (hd.symm _ _ x (Finmap.mem_of_lookup_eq_some hx))).trans hx) hv
      obtain ⟨A, B, h, t, rfl, hab, hea, hch, hth, htt, hshape', hft⟩ :=
        hfr.expose_minimum htr hfree.2 heΘ
          (fun hdone => Capability.dual_active ha (hdual.2.done_iff.mp hdone)) hminΘ
      obtain ⟨hΛA, hΛB⟩ := (Finmap.disjoint_union_right Λ A B).mp hd
      have hwhole : Conversion.Compatible ((Λ ∪ A) ∪ B) := by
        rw [Finmap.union_assoc]
        exact hb.compatible
      have hname : e.opposite.name = e.name := rfl
      rw [hname] at hshape'
      obtain ⟨q, hs⟩ := same_name_linear_guards_step htg hth hΛA hwhole.union_left
        (htg.separated e c heg) hshape hshape'
      have hc : Cong p (.par (.par g h) t) :=
        Cong.trans hcg (Cong.trans (Cong.par_cong (Cong.refl g) hch)
          (Cong.par_assoc g h t).symm)
      exact Or.inr ⟨.par q t, PiCalculus.Step.cong hc (PiCalculus.Step.parL hs) (Cong.refl _)⟩
    · have hcomplete : Δ.Completed := by
        intro e c he
        by_contra ha
        exact hactive ⟨e, c, he, ha⟩
      exact Or.inl (hf.completed_idle ht hreq hcomplete)
  · exact Or.inr (hf.request_progress hreq hav)

end Cslib.SessionTypes.Endpoint.Runtime
