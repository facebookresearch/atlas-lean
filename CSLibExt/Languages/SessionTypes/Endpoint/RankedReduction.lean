/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedCommunication

/-!
# Ranked subject reduction on every canonical π step at compatible interfaces
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- From a ranked-typed source with an initially compatible interface, every
actual canonical step preserves the refinement and compatibility, with zero
or one actual external matched subject advancement.
Private head/continuation changes are derived from faithful bound projection. -/
theorem RankedType.subject_reduction {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ p) (hco : Compatible Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, RankedType n Ξ q ∧ Compatible Ξ ∧ (Ξ = Δ ∨ DualAdvance Δ Ξ) := by
  induction hs generalizing n Δ with
  | commSelect hp hq =>
    have hf := h.hasType.finiteLinear
    have hep := finiteLinear_select_eq hp hf.1
    have heq := finiteLinear_select_eq hq hf.2
    rw [hep, heq] at h
    obtain ⟨Ξ, ha, ht, hc⟩ := h.head_comm_advance hco
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
    · rcases ha.project_bind_faithful with ⟨d, hr, hprivate, rfl⟩ | ⟨Δ', hd, rfl⟩
      · exact ⟨Δ, RankedType.nu (c := d) ht, hco, Or.inl rfl⟩
      · exact ⟨Δ', RankedType.nu (c := c) ht, hd.compatible hco, Or.inr hd⟩
  | cong hp hs hq ih =>
    have ht := (RankedType.cong_iff hp).mp h
    obtain ⟨Ξ, hr, hc, he⟩ := ih ht hco
    exact ⟨Ξ, (RankedType.cong_iff hq).mp hr, hc, he⟩

/-- For a ranked-typed source, initial balance supplies compatibility and is
preserved by the actual canonical step and its exact update. -/
theorem RankedType.subject_reduction_balanced {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ p) (hb : Balanced Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, RankedType n Ξ q ∧ Balanced Ξ ∧ (Ξ = Δ ∨ DualAdvance Δ Ξ) := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction hb.compatible hs
  have hbal : Balanced Ξ := by
    rcases he with rfl | ha
    · exact hb
    · exact ha.balanced hb
  exact ⟨Ξ, ht, hbal, he⟩

/-- Empty-interface ranked typing is preserved by any canonical step at any
ambient depth and through pre/post congruence. The empty context supplies
balance and therefore the required compatibility. -/
theorem RankedType.subject_reduction_empty {n : Nat} {p q : Proc}
    (h : RankedType n ∅ p) (hs : PiCalculus.Step p q) : RankedType n ∅ q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction balanced_empty.compatible hs
  rcases he with rfl | ha
  · exact ht
  · cases ha with
    | matched hl => simp at hl

end Cslib.SessionTypes.Endpoint
