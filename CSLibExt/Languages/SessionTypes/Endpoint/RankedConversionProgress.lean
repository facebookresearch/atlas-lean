/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionFrontier

/-! # Actual communication from semantic-balanced conversion guard frontiers -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

private theorem semantic_sends_not_sends {c d : Capability} {s t : Protocol}
    (hs : SendsTo c s) (he : d.Equivalent c.dual) (ht : SendsTo d t) : False := by
  rcases hs with hs | ⟨r, k, v, hs⟩
  · obtain ⟨u, hu, hr⟩ := passive_peer_head he hs
    rcases ht with ht | ⟨r', k', v', ht⟩ <;> rw [hu] at ht <;> cases ht
  · obtain ⟨v', u, hu, hv, hr⟩ := endpoint_peer_head he hs
    rcases ht with ht | ⟨r', k', v', ht⟩ <;> rw [hu] at ht <;> cases ht

private theorem output_send {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c s := by
  obtain ⟨e, c, hn, hc, hs⟩ := h.hasType.out_inv
  rcases hs with ⟨s, hs⟩ | ⟨d, v, k, t, s, hdn, hd, hs, hv⟩
  · exact ⟨e, c, s, hn, hc, Or.inl hs⟩
  · exact ⟨e, c, s, hn, hc, Or.inr ⟨_, _, _, hs⟩⟩

private theorem input_dual_send {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c.dual s := by
  obtain ⟨e, c, hn, hc, hs⟩ := h.inp_inv
  rcases hs with ⟨s, hs, hp⟩ | ⟨r, k, v, s, hs, hp⟩
  · refine ⟨e, c, s.dual, hn, hc, Or.inl ?_⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl
  · refine ⟨e, c, s.dual, hn, hc, Or.inr ⟨r, k, v, ?_⟩⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl

/-- For disjoint ranked-typed same-name leaves at a semantically compatible
combined interface, literal guard shapes have opposite directions and yield
an actual canonical Step. -/
theorem same_name_guards_step {n : Nat} {Γ Θ : Context} {g h : Proc} {a : Name}
    (hg : RankedType n Γ g) (hh : RankedType n Θ h)
    (hd : Finmap.Disjoint Γ Θ) (hc : Compatible (Γ ∪ Θ))
    (sg : (∃ b p, g = .out a b p) ∨ (∃ p, g = .inp a p))
    (sh : (∃ b p, h = .out a b p) ∨ (∃ p, h = .inp a p)) :
    ∃ q, PiCalculus.Step (.par g h) q := by
  rcases sg with ⟨b, p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases sh with ⟨d, q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨e, c, s, hn, he, hs⟩ := output_send hg
    obtain ⟨f, u, t, hm, hf, ht⟩ := output_send hh
    exact False.elim (semantic_sends_not_sends hs
      (communicating_equivalent hd he hf (hn.trans hm.symm) hc) ht)
  · exact ⟨_, PiCalculus.Step.commSelect (.refl _) (.refl _)⟩
  · exact ⟨_, PiCalculus.Step.cong (Cong.par_comm _ _)
      (PiCalculus.Step.commSelect (.refl _) (.refl _)) (Cong.refl _)⟩
  · obtain ⟨e, c, s, hn, he, hs⟩ := input_dual_send hg
    obtain ⟨f, u, t, hm, hf, ht⟩ := input_dual_send hh
    have hu := communicating_equivalent hd he hf (hn.trans hm.symm) hc
    have hud : u.dual.Equivalent c.dual.dual := hu.dual
    exact False.elim (semantic_sends_not_sends hs hud ht)

/-- GENERAL balanced ranked frontier progress. A minimum over ALL active
owned roles exposes two distinct opposite subject leaves, from which actual
canonical communication follows. Completion is process-level Cong to nil. -/
theorem GuardFrontier.progress {n : Nat} {Δ : Context} {p : Proc}
    (hf : GuardFrontier p) (ht : RankedType n Δ p) (hb : Balanced Δ) :
    Cong p .nil ∨ ∃ q, PiCalculus.Step p q := by
  classical
  by_cases hactive : ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done
  · obtain ⟨e, c, he, ha, hmin⟩ := Context.active_minimum hactive
    obtain ⟨Γ, Θ, g, r, rfl, hd, heg, hcg, htg, htr, hshape, hfr⟩ :=
      GuardFrontier.expose_minimum hf ht he ha hmin
    obtain ⟨d, hep, hdual⟩ := hb e c he
    have hminΓ : ∀ x v, Γ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
      intro x v hx hv
      exact hmin x v ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)).trans hx) hv
    have hnot : e.opposite ∉ Γ := by
      intro hem
      rw [Finmap.lookup_union_left hem] at hep
      exact minimum_peer_separate htg heg ha hminΓ hshape hdual hep
    have heΘ : Θ.lookup e.opposite = some d := by
      rw [Finmap.lookup_union_right hnot] at hep
      exact hep
    have hminΘ : ∀ x v, Θ.lookup x = some v → v.protocol.unfold ≠ .done →
        d.rank ≤ v.rank := by
      intro x v hx hv
      have hn : x ∉ Γ := hd.symm _ _ x (Finmap.mem_of_lookup_eq_some hx)
      have hr : d.rank = c.rank := hdual.1
      rw [hr]
      exact hmin x v ((Finmap.lookup_union_right hn).trans hx) hv
    obtain ⟨A, B, h, t, rfl, hab, hea, hch, hth, htt, hshape', hft⟩ :=
      GuardFrontier.expose_minimum hfr htr heΘ
        (fun hd => Capability.dual_active ha (hdual.2.done_iff.mp hd)) hminΘ
    obtain ⟨hΓA, hΓB⟩ := (Finmap.disjoint_union_right Γ A B).mp hd
    have hwhole : Compatible ((Γ ∪ A) ∪ B) := by
      rw [Finmap.union_assoc]
      exact hb.compatible
    have hname : e.opposite.name = e.name := rfl
    rw [hname] at hshape'
    obtain ⟨q, hs⟩ := same_name_guards_step htg hth hΓA hwhole.union_left hshape hshape'
    have hc : Cong p (.par (.par g h) t) :=
      Cong.trans hcg (Cong.trans (Cong.par_cong (Cong.refl g) hch)
        (Cong.symm (Cong.par_assoc g h t)))
    exact Or.inr ⟨.par q t, PiCalculus.Step.cong hc (PiCalculus.Step.parL hs) (Cong.refl _)⟩
  · have hc : Δ.Completed := by
      intro e c he
      by_contra ha
      exact hactive ⟨e, c, he, ha⟩
    exact Or.inl (GuardFrontier.completed_nil hf ht hc)


end Cslib.SessionTypes.Endpoint.Conversion
