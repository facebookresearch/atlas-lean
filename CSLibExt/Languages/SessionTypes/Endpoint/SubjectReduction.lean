/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.AdvanceProjection
public import CSLibExt.Languages.SessionTypes.Endpoint.CongTyping

/-!
# Subject reduction for every canonical π reduction constructor
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Injective physical-name rekeying retains partial dual compatibility. -/
theorem Compatible.rekey {Δ : Context} {f : Name → Name}
    (h : Compatible Δ) (hf : Function.Injective f)
    (hi : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    Compatible (Context.rekey (Key.mapName f) Δ hi) := by
  intro e c d hc hd
  obtain ⟨a, ha, rfl⟩ := Context.lookup_rekey.mp hc
  obtain ⟨b, hb, he⟩ := Context.lookup_rekey.mp hd
  have hkey : b = a.opposite := Key.mapName_injective hf he
  subst b
  exact h a c d ha hb

/-- A fresh complete bound pair extends any ordinary compatible interface. -/
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
        have hf := Context.unique hv (Context.lookup_bind_negative c Δ)
        subst u
        subst v
        rfl
      | negative =>
        have he := Context.unique hu (Context.lookup_bind_negative c Δ)
        have hf := Context.unique hv (Context.lookup_bind_positive c Δ)
        subst u
        subst v
        exact c.dual_dual.symm
  · let d := Key.mapName (substName (.const 0) 0) e
    have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
    have hu' : Δ.lookup d = some u := (Context.lookup_bind_outer (c := c)).mp (he ▸ hu)
    have he' : Key.mapName (liftName 0) d.opposite = e.opposite := congrArg Key.opposite he
    have hv' : Δ.lookup d.opposite = some v :=
      (Context.lookup_bind_outer (c := c) (e := d.opposite)).mp (he' ▸ hv)
    exact h d u v hu' hv'

/-- All five canonical reduction constructors preserve typing with exactly
one matched external subject-pair advancement or an unchanged interface when
communication is private. No fragment or enabled-edge premise is required. -/
theorem HasType.subject_reduction {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ p) (hco : Compatible Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Ξ q ∧ Compatible Ξ ∧ (Ξ = Δ ∨ DualAdvance Δ Ξ) := by
  induction hs generalizing n Δ with
  | commSelect hp hq =>
    have hf := h.finiteLinear
    have hep := finiteLinear_select_eq hp hf.1
    have heq := finiteLinear_select_eq hq hf.2
    rw [hep, heq] at h
    obtain ⟨Ξ, ha, ht, hc⟩ := h.head_comm_advance hco
    exact ⟨Ξ, ht, hc, Or.inr ha⟩
  | parL hs ih =>
    obtain ⟨Γ, Θ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp hco.union_left
    rcases he with rfl | ha
    · exact ⟨_, HasType.par hd ht hq, hco, Or.inl rfl⟩
    · have hau := ha.frame_left (Θ := Θ)
      exact ⟨Ξ ∪ Θ, HasType.par (ha.disjoint_frame hd) ht hq,
        hau.compatible hco, Or.inr hau⟩
  | parR hs ih =>
    obtain ⟨Θ, Γ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hq (hco.union_right hd)
    rcases he with rfl | ha
    · exact ⟨_, HasType.par hd hp ht, hco, Or.inl rfl⟩
    · have hau := ha.frame_right hd
      exact ⟨Θ ∪ Ξ, HasType.par ((ha.disjoint_frame (hd.symm _ _)).symm _ _) hp ht,
        hau.compatible hco, Or.inr hau⟩
  | nu hs ih =>
    obtain ⟨c, hp⟩ := h.nu_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp (hco.bind c)
    rcases he with rfl | ha
    · exact ⟨Δ, HasType.nu ht, hco, Or.inl rfl⟩
    · rcases ha.project_bind with ⟨d, hr, rfl⟩ | ⟨Δ', hd, rfl⟩
      · exact ⟨Δ, HasType.nu ht, hco, Or.inl rfl⟩
      · exact ⟨Δ', HasType.nu ht, hd.compatible hco, Or.inr hd⟩
  | cong hp hs hq ih =>
    have ht := (HasType.cong_iff hp).mp h
    obtain ⟨Ξ, hr, hc, he⟩ := ih ht hco
    exact ⟨Ξ, (HasType.cong_iff hq).mp hr, hc, he⟩

/-- Balanced initial interfaces remain balanced after any canonical step,
with the same exact zero-or-one external advancement evidence. -/
theorem HasType.subject_reduction_balanced {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ p) (hb : Balanced Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Ξ q ∧ Balanced Ξ ∧ (Ξ = Δ ∨ DualAdvance Δ Ξ) := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction hb.compatible hs
  have hbal : Balanced Ξ := by
    rcases he with rfl | ha
    · exact hb
    · exact ha.balanced hb
  exact ⟨Ξ, ht, hbal, he⟩

/-- A communication behind any number of restrictions cannot create an
external endpoint in a network whose original interface is empty. -/
theorem HasType.subject_reduction_empty {n : Nat} {p q : Proc}
    (h : HasType n ∅ p) (hs : PiCalculus.Step p q) : HasType n ∅ q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction balanced_empty.compatible hs
  rcases he with rfl | ha
  · exact ht
  · cases ha with
    | matched hl => simp at hl

end Cslib.SessionTypes.Endpoint
