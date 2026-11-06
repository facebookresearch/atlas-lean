/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.FrontierMinimum

/-!
# Actual communication from balanced ranked guard frontiers
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

private theorem sends_dual_not_sends {c : Capability} {s t : Protocol}
    (hs : SendsTo c s) (ht : SendsTo c.dual t) : False := by
  rcases hs with hs | ⟨r, k, v, hs⟩ <;>
    rcases ht with ht | ⟨r', k', v', ht⟩
  all_goals
    change c.protocol.dual.unfold = _ at ht
    rw [Protocol.unfold_dual, hs] at ht
    cases ht

private theorem ranked_output_send {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c s := by
  obtain ⟨e, c, hn, hc, hg, hs⟩ := h.out_inv
  rcases hs with ⟨s, hs, hp⟩ | ⟨d, k, v, s, hd, hs, hv, he, hp⟩
  · exact ⟨e, c, s, hn, hc, Or.inl hs⟩
  · exact ⟨e, c, s, hn, hc, Or.inr ⟨_, _, _, hs⟩⟩

private theorem ranked_input_dual_send {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c.dual s := by
  obtain ⟨e, c, hn, hc, hg, hs⟩ := h.inp_inv
  rcases hs with ⟨s, hs, hp⟩ | ⟨r, k, v, s, hs, hp⟩
  · refine ⟨e, c, s.dual, hn, hc, Or.inl ?_⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl
  · refine ⟨e, c, s.dual, hn, hc, Or.inr ⟨r, k, v, ?_⟩⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl

/-- **Same-name ranked guards are opposite and communicate.**
Given disjoint ranked-typed leaves with literal same-name input/output
guard shapes and a compatible combined interface, their directions are opposite.
The Step is canonical commSelect, possibly after parallel commutation. -/
theorem same_name_guards_step {n : Nat} {Γ Θ : Context} {g h : Proc} {a : Name}
    (hg : RankedType n Γ g) (hh : RankedType n Θ h)
    (hd : Finmap.Disjoint Γ Θ) (hc : Compatible (Γ ∪ Θ))
    (sg : (∃ b p, g = .out a b p) ∨ (∃ p, g = .inp a p))
    (sh : (∃ b p, h = .out a b p) ∨ (∃ p, h = .inp a p)) :
    ∃ q, PiCalculus.Step (.par g h) q := by
  rcases sg with ⟨b, p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases sh with ⟨d, q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨e, c, s, hn, he, hs⟩ := ranked_output_send hg
    obtain ⟨f, u, t, hm, hf, ht⟩ := ranked_output_send hh
    have hu := communicating_capabilities_dual hd he hf (hn.trans hm.symm) hc
    subst u
    exact False.elim (sends_dual_not_sends hs ht)
  · exact ⟨_, PiCalculus.Step.commSelect (.refl _) (.refl _)⟩
  · exact ⟨_, PiCalculus.Step.cong (Cong.par_comm _ _)
      (PiCalculus.Step.commSelect (.refl _) (.refl _)) (Cong.refl _)⟩
  · obtain ⟨e, c, s, hn, he, hs⟩ := ranked_input_dual_send hg
    obtain ⟨f, u, t, hm, hf, ht⟩ := ranked_input_dual_send hh
    have hu := communicating_capabilities_dual hd he hf (hn.trans hm.symm) hc
    subst u
    rw [Capability.dual_dual] at ht
    exact False.elim (sends_dual_not_sends ht hs)

/-- **Progress for balanced ranked guard frontiers.**
GENERAL balanced ranked frontier progress. A minimum over ALL active
owned roles exposes two distinct opposite subject leaves, from which actual
canonical communication follows. Completion is process-level Cong to nil. -/
theorem GuardFrontier.progress {n : Nat} {Δ : Context} {p : Proc}
    (hf : GuardFrontier p) (ht : RankedType n Δ p) (hb : Balanced Δ) :
    Cong p .nil ∨ ∃ q, PiCalculus.Step p q := by
  classical
  by_cases hactive : ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done
  · obtain ⟨e, c, he, ha, hmin⟩ := Context.active_minimum hactive
    obtain ⟨Γ, Θ, g, r, rfl, hd, heg, hcg, htg, htr, hshape, hfr⟩ :=
      hf.expose_minimum ht he ha hmin
    have hep : (Γ ∪ Θ).lookup e.opposite = some c.dual := hb e c he
    have hminΓ : ∀ x v, Γ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
      intro x v hx hv
      exact hmin x v ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)).trans hx) hv
    have hnot : e.opposite ∉ Γ := by
      intro hem
      rw [Finmap.lookup_union_left hem] at hep
      exact minimum_peer_separate htg heg ha hminΓ hshape hep
    have heΘ : Θ.lookup e.opposite = some c.dual := by
      rw [Finmap.lookup_union_right hnot] at hep
      exact hep
    have hminΘ : ∀ x v, Θ.lookup x = some v → v.protocol.unfold ≠ .done →
        c.dual.rank ≤ v.rank := by
      intro x v hx hv
      have hn : x ∉ Γ := hd.symm _ _ x (Finmap.mem_of_lookup_eq_some hx)
      exact hmin x v ((Finmap.lookup_union_right hn).trans hx) hv
    obtain ⟨A, B, h, t, rfl, hab, hea, hch, hth, htt, hshape', hft⟩ :=
      hfr.expose_minimum htr heΘ (Capability.dual_active ha) hminΘ
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
    exact Or.inl (hf.completed_nil ht hc)

/-- **Binding a fresh dual pair preserves balance.**
A fresh private pair preserves full dual ownership of an outer balanced
interface. Every nonfresh owned role is reflected through canonical lifting. -/
theorem Balanced.bind {Δ : Context} (h : Balanced Δ) (c : Capability) :
    Balanced (Context.bind c Δ) := by
  intro e u hu
  by_cases hn : e.name = .var 0
  · cases e with
    | mk a r =>
      change a = .var 0 at hn
      subst a
      cases r with
      | positive =>
        have hc := Context.unique hu (Context.lookup_bind_positive c Δ)
        subst u
        exact Context.lookup_bind_negative c Δ
      | negative =>
        have hc := Context.unique hu (Context.lookup_bind_negative c Δ)
        subst u
        rw [Capability.dual_dual]
        exact Context.lookup_bind_positive c Δ
  · let d := Key.mapName (substName (.const 0) 0) e
    have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
    have hd : Δ.lookup d = some u := (Context.lookup_bind_outer (c := c)).mp (he ▸ hu)
    have he' : Key.mapName (liftName 0) d.opposite = e.opposite := congrArg Key.opposite he
    rw [← he']
    exact Context.lookup_bind_outer.mpr (h d u hd)

end Cslib.SessionTypes.Endpoint
