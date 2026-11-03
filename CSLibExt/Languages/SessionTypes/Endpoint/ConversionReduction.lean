/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticProjection
public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionCong

/-!
# Canonical Step preservation at semantically compatible conversion interfaces

All five cases use the new congruence/substitution/head proofs and exact
semantic advancement, not the raw judgement's preservation theorem.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- From a typed source at an initially compatible interface, all five
canonical reduction constructors preserve typing and compatibility, with one
matched external subject-pair advancement or an unchanged interface when
communication is private. No fragment or enabled-edge premise is required. -/
theorem HasType.subject_reduction {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ p) (hco : Compatible Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Ξ q ∧ Compatible Ξ ∧ (Ξ = Δ ∨ SemanticAdvance Δ Ξ) := by
  induction hs generalizing n Δ with
  | commSelect hp hq =>
    have hf := h.finiteLinear
    have hep := finiteLinear_select_eq hp hf.1
    have heq := finiteLinear_select_eq hq hf.2
    rw [hep, heq] at h
    obtain ⟨Ξ, ht, hc, ha⟩ := h.head_advance hco
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
    · rcases ha.project_bind with ⟨d, hr, hprivate, rfl⟩ | ⟨Δ', hd, rfl⟩
      · exact ⟨Δ, HasType.nu ht, hco, Or.inl rfl⟩
      · exact ⟨Δ', HasType.nu ht, hd.compatible hco, Or.inr hd⟩
  | cong hp hs hq ih =>
    have ht := (HasType.cong_iff hp).mp h
    obtain ⟨Ξ, hr, hc, he⟩ := ih ht hco
    exact ⟨Ξ, (HasType.cong_iff hq).mp hr, hc, he⟩

/-- A typed source with a balanced initial interface retains typing and balance
after any canonical step. Balance supplies the required compatibility; the
exact zero-or-one external advancement evidence is retained. -/
theorem HasType.subject_reduction_balanced {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ p) (hb : Balanced Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Ξ q ∧ Balanced Ξ ∧ (Ξ = Δ ∨ SemanticAdvance Δ Ξ) := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction hb.compatible hs
  have hbal : Balanced Ξ := by
    rcases he with rfl | ha
    · exact hb
    · exact ha.balanced hb
  exact ⟨Ξ, ht, hbal, he⟩

/-- An empty-interface typed network retains empty-interface typing through
any canonical step. The empty context is balanced, hence compatible, including
communication behind restrictions and pre/post congruence. -/
theorem HasType.subject_reduction_empty {n : Nat} {p q : Proc}
    (h : HasType n ∅ p) (hs : PiCalculus.Step p q) : HasType n ∅ q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction balanced_empty.compatible hs
  rcases he with rfl | ha
  · exact ht
  · cases ha with
    | matched hl => simp at hl


/-- A typed source at an initially semantically compatible interface retains
typing and compatibility through finite actual execution, with a finite trace
of faithful advances. This is safety, not progress or termination. -/
theorem HasType.reachable {n : Nat} {Δ : Context} {p q : Proc} (h : HasType n Δ p)
    (hc : Compatible Δ) (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    ∃ Ξ, HasType n Ξ q ∧ Compatible Ξ ∧ Relation.ReflTransGen SemanticAdvance Δ Ξ := by
  induction hr with
  | refl => exact ⟨Δ, h, hc, .refl⟩
  | tail hr hs ih =>
    obtain ⟨Θ, ht, hc, ha⟩ := ih
    obtain ⟨Ξ, hq, hco, he⟩ := ht.subject_reduction hc hs
    rcases he with rfl | he
    · exact ⟨_, hq, hco, ha⟩
    · exact ⟨Ξ, hq, hco, ha.tail he⟩

/-- Every finite reachable closed state retains the exact empty interface. -/
theorem HasType.reachable_empty {n : Nat} {p q : Proc} (h : HasType n ∅ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) : HasType n ∅ q := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact ih.subject_reduction_empty hs

end Cslib.SessionTypes.Endpoint.Conversion
