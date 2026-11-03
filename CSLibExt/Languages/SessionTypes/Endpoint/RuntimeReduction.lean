/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCommunication
public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCong
public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticProjection

/-!
# Canonical runtime reduction at initially compatible interfaces

Replicas remain genuine runtime syntax, never erased to finite typing. Shared
communication preserves exact ownership; linear communication advances faithfully.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Canonical choice selection is identity on an actually runtime-typed root:
there is no sum rule, although replication is admitted. No finiteLinear erasure. -/
theorem HasType.select_eq {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hs : Select p q) : p = q := by
  induction hs with
  | refl => rfl
  | left => cases h
  | right => cases h
  | trans hp hq ihp ihq =>
    have he := ihp h
    exact he.trans (ihq (he ▸ h))

/-- From a runtime-typed source at an INITIALLY semantically compatible linear
interface, ALL5 canonical Step constructors preserve Γ/n, typing and compatibility.
The actual residual interface is unchanged OR has one faithful SemanticAdvance.
Shared transfers are exact identity; private projection uses the chosen literal pair. -/
theorem HasType.subject_reduction {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hco : Conversion.Compatible Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Γ Ξ q ∧ Conversion.Compatible Ξ ∧
      (Ξ = Δ ∨ Conversion.SemanticAdvance Δ Ξ) := by
  induction hs generalizing n Δ with
  | commSelect hp hq =>
    obtain ⟨Λ, Θ, hsplit, hd, hleft, hright⟩ := h.par_inv
    have hep := hleft.select_eq hp
    have heq := hright.select_eq hq
    rw [hep, heq] at h
    exact h.head_advance hco
  | parL hs ih =>
    obtain ⟨Λ, Θ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp hco.union_left
    rcases he with rfl | ha
    · exact ⟨_, HasType.par hd ht hq, hco, Or.inl rfl⟩
    · have hau := ha.frame_left (Θ := Θ)
      exact ⟨Ξ ∪ Θ, HasType.par (ha.disjoint_frame hd) ht hq,
        hau.compatible hco, Or.inr hau⟩
  | parR hs ih =>
    obtain ⟨Θ, Λ, rfl, hd, hp, hq⟩ := h.par_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hq (hco.union_right hd)
    rcases he with rfl | ha
    · exact ⟨_, HasType.par hd hp ht, hco, Or.inl rfl⟩
    · have hau := ha.frame_right hd
      exact ⟨Θ ∪ Ξ, HasType.par ((ha.disjoint_frame (hd.symm _ _)).symm _ _) hp ht,
        hau.compatible hco, Or.inr hau⟩
  | nu hs ih =>
    have hsep := h.separated
    obtain ⟨c, hp⟩ := h.nu_inv
    obtain ⟨Ξ, ht, hc, he⟩ := ih hp (hco.bind c)
    rcases he with rfl | ha
    · exact ⟨Δ, HasType.nu hsep ht, hco, Or.inl rfl⟩
    · rcases ha.project_bind with ⟨d, hr, hprivate, rfl⟩ | ⟨Δ', hd, rfl⟩
      · exact ⟨Δ, HasType.nu hsep ht, hco, Or.inl rfl⟩
      · exact ⟨Δ', HasType.nu (hsep.advance hd) ht, hd.compatible hco, Or.inr hd⟩
  | cong hp hs hq ih =>
    have ht := (HasType.cong_iff hp).mp h
    obtain ⟨Ξ, hr, hc, he⟩ := ih ht hco
    exact ⟨Ξ, (HasType.cong_iff hq).mp hr, hc, he⟩

/-- An INITIALLY semantically balanced runtime interface derives compatibility
and retains balance and the exact zero-or-one external advance after ANY Step. -/
theorem HasType.subject_reduction_balanced {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hb : Conversion.Balanced Δ) (hs : PiCalculus.Step p q) :
    ∃ Ξ, HasType n Γ Ξ q ∧ Conversion.Balanced Ξ ∧
      (Ξ = Δ ∨ Conversion.SemanticAdvance Δ Ξ) := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction hb.compatible hs
  have hbal : Conversion.Balanced Ξ := by
    rcases he with rfl | ha
    · exact hb
    · exact ha.balanced hb
  exact ⟨Ξ, ht, hbal, he⟩

/-- An empty linear interface is initially balanced/compatible and remains EXACTLY
empty through any runtime Step, including private sessions and shared services. -/
theorem HasType.subject_reduction_empty {n : Nat} {Γ : ServiceEnv} {p q : Proc}
    (h : HasType n Γ ∅ p) (hs : PiCalculus.Step p q) : HasType n Γ ∅ q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction Conversion.balanced_empty.compatible hs
  rcases he with rfl | ha
  · exact ht
  · cases ha with
    | matched hl => simp at hl

/-- From an INITIALLY compatible runtime interface, finite actual reductions
retain typing/compatibility and accumulate a trace of faithful semantic advances.
Shared/private identity steps introduce no fake external advancement. -/
theorem HasType.reachable {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hc : Conversion.Compatible Δ)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    ∃ Ξ, HasType n Γ Ξ q ∧ Conversion.Compatible Ξ ∧
      Relation.ReflTransGen Conversion.SemanticAdvance Δ Ξ := by
  induction hr with
  | refl => exact ⟨Δ, h, hc, .refl⟩
  | tail hr hs ih =>
    obtain ⟨Θ, ht, hc, ha⟩ := ih
    obtain ⟨Ξ, hq, hco, he⟩ := ht.subject_reduction hc hs
    rcases he with rfl | he
    · exact ⟨_, hq, hco, ha⟩
    · exact ⟨Ξ, hq, hco, ha.tail he⟩

/-- Every finite reachable state from an INITIALLY balanced runtime interface
retains semantic balance and an ACTUAL faithful advancement trace, not progress. -/
theorem HasType.reachable_balanced {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hb : Conversion.Balanced Δ)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    ∃ Ξ, HasType n Γ Ξ q ∧ Conversion.Balanced Ξ ∧
      Relation.ReflTransGen Conversion.SemanticAdvance Δ Ξ := by
  obtain ⟨Ξ, ht, hc, ha⟩ := h.reachable hb.compatible hr
  have hbal : Conversion.Balanced Ξ := by
    clear ht hc
    induction ha with
    | refl => exact hb
    | tail ha hs ih => exact hs.balanced ih
  exact ⟨Ξ, ht, hbal, ha⟩

/-- Finite runtime execution from an empty interface preserves exact empty
ownership. This safety result does not identify idle replicas with Cong nil. -/
theorem HasType.reachable_empty {n : Nat} {Γ : ServiceEnv} {p q : Proc}
    (h : HasType n Γ ∅ p) (hr : Relation.ReflTransGen PiCalculus.Step p q) : HasType n Γ ∅ q := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact ih.subject_reduction_empty hs

end Cslib.SessionTypes.Endpoint.Runtime
