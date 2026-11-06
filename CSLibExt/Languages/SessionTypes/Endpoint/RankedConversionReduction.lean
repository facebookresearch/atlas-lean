/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionCommunication
public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticProjection

/-!
# Ranked canonical Step preservation at semantically compatible interfaces

All five cases use the new congruence/substitution/head proofs and exact
semantic advancement, not the raw judgement's preservation theorem.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Conversion ranked subject reduction at compatible interfaces.**
From a typed source at an initially compatible interface, all five
canonical reduction constructors preserve typing and compatibility, with one
matched external subject-pair advancement or an unchanged interface when
communication is private. No fragment or enabled-edge premise is required. -/
theorem RankedType.subject_reduction {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ p) (hco : Compatible Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, RankedType n Ξ q ∧ Compatible Ξ ∧ (Ξ = Δ ∨ SemanticAdvance Δ Ξ) := by
  induction hs generalizing n Δ with
  | commSelect hp hq =>
    have hf := h.hasType.finiteLinear
    have hep := finiteLinear_select_eq hp hf.1
    have heq := finiteLinear_select_eq hq hf.2
    rw [hep, heq] at h
    obtain ⟨Ξ, ht, hc, ha⟩ := h.head_advance hco
    exact ⟨Ξ, ht, hc, Or.inr ha⟩
  | parL hs ih =>
    obtain ⟨Γ, Θ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp hco.union_left
    rcases he with rfl | ha
    · exact ⟨_, RankedType.par hd ht hq, hco, Or.inl rfl⟩
    · have hau := ha.frame_left (Θ := Θ)
      exact ⟨Ξ ∪ Θ, RankedType.par (ha.disjoint_frame hd) ht hq,
        hau.compatible hco, Or.inr hau⟩
  | parR hs ih =>
    obtain ⟨Θ, Γ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hq (hco.union_right hd)
    rcases he with rfl | ha
    · exact ⟨_, RankedType.par hd hp ht, hco, Or.inl rfl⟩
    · have hau := ha.frame_right hd
      exact ⟨Θ ∪ Ξ, RankedType.par ((ha.disjoint_frame (hd.symm _ _)).symm _ _) hp ht,
        hau.compatible hco, Or.inr hau⟩
  | nu hs ih =>
    obtain ⟨c, hp⟩ := h.nu_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp (hco.bind c)
    rcases he with rfl | ha
    · exact ⟨Δ, RankedType.nu ht, hco, Or.inl rfl⟩
    · rcases ha.project_bind with ⟨d, hr, hprivate, rfl⟩ | ⟨Δ', hd, rfl⟩
      · exact ⟨Δ, RankedType.nu ht, hco, Or.inl rfl⟩
      · exact ⟨Δ', RankedType.nu ht, hd.compatible hco, Or.inr hd⟩
  | cong hp hs hq ih =>
    have ht := (RankedType.cong_iff hp).mp h
    obtain ⟨Ξ, hr, hc, he⟩ := ih ht hco
    exact ⟨Ξ, (RankedType.cong_iff hq).mp hr, hc, he⟩

/-- **Conversion ranked subject reduction at balanced interfaces.**
A typed source with a balanced initial interface retains typing and balance
after any canonical step. Balance supplies the required compatibility; the
exact zero-or-one external advancement evidence is retained. -/
theorem RankedType.subject_reduction_balanced {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ p) (hb : Balanced Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, RankedType n Ξ q ∧ Balanced Ξ ∧ (Ξ = Δ ∨ SemanticAdvance Δ Ξ) := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction hb.compatible hs
  have hbal : Balanced Ξ := by
    rcases he with rfl | ha
    · exact hb
    · exact ha.balanced hb
  exact ⟨Ξ, ht, hbal, he⟩

/-- **Conversion ranked subject reduction at the empty interface.**
An empty-interface typed network retains empty-interface typing through
any canonical step. The empty context is balanced, hence compatible, including
communication behind restrictions and pre/post congruence. -/
theorem RankedType.subject_reduction_empty {n : Nat} {p q : Proc}
    (h : RankedType n ∅ p) (hs : PiCalculus.Step p q) : RankedType n ∅ q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction balanced_empty.compatible hs
  rcases he with rfl | ha
  · exact ht
  · cases ha with
    | matched hl => simp at hl


/-- **Finite runs keep conversion ranked typing at compatible interfaces.**
A ranked-typed source at an initially semantically compatible interface
retains typing and compatibility through finite actual execution, with a finite
trace of faithful advances. This is safety, not progress or termination. -/
theorem RankedType.reachable {n : Nat} {Δ : Context} {p q : Proc} (h : RankedType n Δ p)
    (hc : Compatible Δ) (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    ∃ Ξ, RankedType n Ξ q ∧ Compatible Ξ ∧ Relation.ReflTransGen SemanticAdvance Δ Ξ := by
  induction hr with
  | refl => exact ⟨Δ, h, hc, .refl⟩
  | tail hr hs ih =>
    obtain ⟨Θ, ht, hc, ha⟩ := ih
    obtain ⟨Ξ, hq, hco, he⟩ := ht.subject_reduction hc hs
    rcases he with rfl | he
    · exact ⟨_, hq, hco, ha⟩
    · exact ⟨Ξ, hq, hco, ha.tail he⟩

/-- **Reachable closed conversion-ranked states keep the empty interface.**
Every finite reachable closed state retains the exact empty interface. -/
theorem RankedType.reachable_empty {n : Nat} {p q : Proc} (h : RankedType n ∅ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) : RankedType n ∅ q := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact ih.subject_reduction_empty hs

end Cslib.SessionTypes.Endpoint.Conversion
