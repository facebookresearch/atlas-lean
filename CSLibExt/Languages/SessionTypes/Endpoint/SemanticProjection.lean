/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticAdvance
public import CSLibExt.Languages.SessionTypes.Endpoint.AdvanceProjection

/-!
# Exact private-versus-external semantic advancement projection

A chosen bound pair is LITERALLY dual. Only this original source fact permits
literal tail equality; semantic duality alone never supplies it.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- Left children inherit actual peer compatibility. -/
theorem Compatible.union_left {Γ Θ : Context} (h : Compatible (Γ ∪ Θ)) : Compatible Γ :=
  fun e c d hc hd => h e c d
    ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc)
    ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hd)).trans hd)

/-- A disjoint right child inherits actual peer compatibility without shadowing. -/
theorem Compatible.union_right {Γ Θ : Context} (h : Compatible (Γ ∪ Θ))
    (hd : Finmap.Disjoint Γ Θ) : Compatible Θ := by
  intro e c d hc hp
  exact h e c d
    ((Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some hc))).trans hc)
    ((Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some hp))).trans hp)

/-- A chosen exact dual private pair extends a semantically compatible interface. -/
theorem Compatible.bind {Δ : Context} (h : Compatible Δ) (c : Capability) :
    Compatible (Context.bind c Δ) := by
  intro e u v hu hv
  by_cases hn : e.name = .var 0
  · cases e with
    | mk a r =>
      change a = .var 0 at hn
      subst a
      cases r with
      | positive =>
        have he := Context.unique hu (Context.lookup_bind_positive c Δ)
        have hp := Context.unique hv (Context.lookup_bind_negative c Δ)
        subst u
        subst v
        exact Capability.Equivalent.refl _
      | negative =>
        have he := Context.unique hu (Context.lookup_bind_negative c Δ)
        have hp := Context.unique hv (Context.lookup_bind_positive c Δ)
        subst u
        subst v
        simpa only [Capability.dual_dual] using Capability.Equivalent.refl c
  · let d := Key.mapName (substName (.const 0) 0) e
    have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
    have hu' : Δ.lookup d = some u := Context.lookup_bind_outer.mp (he ▸ hu)
    have hep : Key.mapName (liftName 0) d.opposite = e.opposite := congrArg Key.opposite he
    have hv' : Δ.lookup d.opposite = some v := Context.lookup_bind_outer.mp (hep ▸ hv)
    exact h d u v hu' hv'

/-- At a semantically balanced outer interface, binding an exact dual private
pair retains balance for the pair and every actual outer peer. -/
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
        have he := Context.unique hu (Context.lookup_bind_positive c Δ)
        subst u
        exact ⟨c.dual, Context.lookup_bind_negative c Δ, Capability.Equivalent.refl _⟩
      | negative =>
        have he := Context.unique hu (Context.lookup_bind_negative c Δ)
        subst u
        exact ⟨c, Context.lookup_bind_positive c Δ, by
          simpa only [Capability.dual_dual] using Capability.Equivalent.refl c⟩
  · let d := Key.mapName (substName (.const 0) 0) e
    have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
    obtain ⟨v, hv, hr⟩ := h d u (Context.lookup_bind_outer.mp (he ▸ hu))
    have hep : Key.mapName (liftName 0) d.opposite = e.opposite := congrArg Key.opposite he
    exact ⟨v, hep ▸ Context.lookup_bind_outer.mpr hv, hr⟩

/-- Faithful projection retains an actual private-pair advance OR the actual
outer advance and unchanged bound pair. It never chooses an arbitrary Xi. -/
theorem SemanticAdvance.project_bind {cap : Capability} {Δ Ξ : Context}
    (h : SemanticAdvance (Context.bind cap Δ) Ξ) :
    (∃ c, c.rank = cap.rank ∧ SemanticAdvance (Context.bind cap ∅) (Context.bind c ∅) ∧
      Ξ = Context.bind c Δ) ∨
    (∃ Δ', SemanticAdvance Δ Δ' ∧ Ξ = Context.bind cap Δ') := by
  cases h with
  | @matched e c d s u hc hd he hh ht =>
    by_cases hn : e.name = .var 0
    · cases e with
      | mk a r =>
        change a = .var 0 at hn
        subst a
        cases r with
        | positive =>
          have hcc := Context.unique hc (Context.lookup_bind_positive cap Δ)
          have hdd := Context.unique hd (Context.lookup_bind_negative cap Δ)
          subst c
          subst d
          have hu := hh.literal_dual_tail rfl
          subst u
          have hraw := DualAdvance.matched (Context.lookup_bind_positive cap ∅)
            (Context.lookup_bind_negative cap ∅) hh.sendsTo
          change DualAdvance (Context.bind cap ∅)
            (((Context.bind cap ∅).insert ⟨.var 0, .positive⟩ ⟨cap.rank, s⟩).insert
              ⟨.var 0, .negative⟩ (⟨cap.rank, s⟩ : Capability).dual) at hraw
          rw [Context.update_bound_positive] at hraw
          exact Or.inl ⟨⟨cap.rank, s⟩, rfl, SemanticAdvance.of_raw hraw,
            Context.update_bound_positive cap ⟨cap.rank, s⟩ Δ⟩
        | negative =>
          have hcc := Context.unique hc (Context.lookup_bind_negative cap Δ)
          have hdd := Context.unique hd (Context.lookup_bind_positive cap Δ)
          subst c
          subst d
          have hu := hh.literal_dual_tail cap.dual_dual.symm
          subst u
          have hp0 : (Context.bind cap ∅).lookup (⟨.var 0, .negative⟩ : Key).opposite =
              some cap.dual.dual := by
            rw [Capability.dual_dual]
            exact Context.lookup_bind_positive cap ∅
          have hraw := DualAdvance.matched (Context.lookup_bind_negative cap ∅) hp0 hh.sendsTo
          have htarget :
              (((Context.bind cap ∅).insert ⟨.var 0, .negative⟩ ⟨cap.rank, s⟩).insert
                ⟨.var 0, .positive⟩ ⟨cap.rank, s.dual⟩) = Context.bind ⟨cap.rank, s.dual⟩ ∅ := by
            simpa only [Capability.dual, Protocol.dual_dual] using
              Context.update_bound_negative cap ⟨cap.rank, s.dual⟩ ∅
          change DualAdvance (Context.bind cap ∅)
            (((Context.bind cap ∅).insert ⟨.var 0, .negative⟩ ⟨cap.rank, s⟩).insert
              ⟨.var 0, .positive⟩ ⟨cap.rank, s.dual⟩) at hraw
          rw [htarget] at hraw
          refine Or.inl ⟨⟨cap.rank, s.dual⟩, rfl, SemanticAdvance.of_raw hraw, ?_⟩
          simpa only [Capability.dual, Protocol.dual_dual, Key.opposite, Role.opposite] using
            Context.update_bound_negative cap ⟨cap.rank, s.dual⟩ Δ
    · let a := Key.mapName (substName (.const 0) 0) e
      have ha : Key.mapName (liftName 0) a = e := Key.lift_subst_outer_name e hn
      have hca : Δ.lookup a = some c := Context.lookup_bind_outer.mp (ha ▸ hc)
      have hap : Key.mapName (liftName 0) a.opposite = e.opposite := congrArg Key.opposite ha
      have hda : Δ.lookup a.opposite = some d := Context.lookup_bind_outer.mp (hap ▸ hd)
      refine Or.inr ⟨(Δ.insert a ⟨c.rank, s⟩).insert a.opposite ⟨d.rank, u⟩,
        SemanticAdvance.matched hca hda he hh ht, ?_⟩
      rw [Context.bind_insert_outer, Context.bind_insert_outer, ha, hap]

/-- An actual outer semantic advance lifts without changing its private pair. -/
theorem SemanticAdvance.bind_outer {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ) (c : Capability) :
    SemanticAdvance (Context.bind c Δ) (Context.bind c Ξ) := by
  cases h with
  | @matched e a b s u ha hb he hh ht =>
    rw [Context.bind_insert_outer, Context.bind_insert_outer]
    exact SemanticAdvance.matched (Context.lookup_bind_outer.mpr ha)
      (Context.lookup_bind_outer.mpr hb) he hh ht

/-- Pointwise semantic recoding retains actual paired domain and cap ranks. -/
theorem Balanced.retype {Δ Ξ : Context} (h : Balanced Δ) (he : ContextEquivalent Δ Ξ) :
    Balanced Ξ := by
  intro e c hc
  obtain ⟨a, ha, hra⟩ := he.symm.lookup hc
  obtain ⟨b, hb, hrb⟩ := h e a ha
  obtain ⟨d, hd, hrd⟩ := he.lookup hb
  exact ⟨d, hd, (hrd.symm.trans hrb).trans hra.dual.symm⟩

/-- Disjoint balanced components form a balanced ownership frame union. -/
theorem Balanced.union {Γ Θ : Context} (hΓ : Balanced Γ) (hΘ : Balanced Θ)
    (hd : Finmap.Disjoint Γ Θ) : Balanced (Γ ∪ Θ) := by
  intro e c hc
  by_cases he : e ∈ Γ
  · rw [Finmap.lookup_union_left he] at hc
    obtain ⟨d, hp, hr⟩ := hΓ e c hc
    exact ⟨d, (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hp)).trans hp, hr⟩
  · rw [Finmap.lookup_union_right he] at hc
    obtain ⟨d, hp, hr⟩ := hΘ e c hc
    have hf : e.opposite ∉ Γ := hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some hp)
    exact ⟨d, (Finmap.lookup_union_right hf).trans hp, hr⟩

end Cslib.SessionTypes.Endpoint.Conversion
