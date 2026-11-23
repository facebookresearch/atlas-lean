/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Weak compatibility bridge for canonical Cslib LTS
-/
module

public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Cslib.Foundations.Semantics.LTS.Divergence

/-!
# Weak compatibility API on canonical CSLib LTS

CSLib has no rooted observational-congruence API. The rooted definitions remain
single CSLibExt extensions in `Cslib.Semantics.LTS`; `RootedSTr` and
`RootedWeakBisimilarity` abbreviate those definitions directly, and the
transfer lemmas below relate saturated multistep transitions, silent closure,
divergence, and saturation. The statements use only the canonical
ambient-`HasTau` API: `τSTr`, `STr`, saturated `MTr` and `SMTr`, and weak
simulation and bisimulation. The former explicit-`tau` reconciliation forms
are not reproduced: with the ambient instance they are the same statements.
-/

@[expose] public section

namespace Cslib.Semantics

namespace LTS

open Cslib.LTS

variable {State Label : Type*} [HasTau Label] {lts : LTS State Label}
  {r : State → State → Prop} {s t : State} {μ : Label} {μs : List Label}

/-! ## Layer 0: rooted extensions on the canonical LTS -/

/-- Rooted weak transition using the ambient silent label. -/
abbrev RootedSTr (l : _root_.Cslib.LTS State Label) :
    State → Label → State → Prop :=
  RootedWeakStep (lts := l)

/-- Rooted weak bisimilarity using the ambient silent label. -/
abbrev RootedWeakBisimilarity (l : _root_.Cslib.LTS State Label) :
    State → State → Prop :=
  RootedWeaklyBisimilar (lts := l)

/-- Rooted weak steps are saturated weak steps. -/
theorem RootedSTr.toSTr [_root_.Cslib.HasTau Label]
    {l : _root_.Cslib.LTS State Label} (h : RootedSTr l s μ t) :
    l.STr s μ t :=
  RootedWeakStep.toSTr h

/-- Rooted silent transitions are exactly nonempty silent runs. -/
theorem rootedSTr_tau_iff_transGen [_root_.Cslib.HasTau Label] :
    RootedSTr lts s _root_.Cslib.HasTau.τ t ↔
      Relation.TransGen (fun a b => lts.Tr a _root_.Cslib.HasTau.τ b) s t := by
  constructor
  · rintro ⟨s₁, s₂, h1, h2, h3⟩
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.TransGen.head' h2 h3
    | @head a b hab _ ih => exact Relation.TransGen.head hab ih
  · intro h
    induction h using Relation.TransGen.head_induction_on with
    | single hstep => exact ⟨_, _, .refl, hstep, .refl⟩
    | @head a b hab _ ih =>
        obtain ⟨s₁, s₂, h1, h2, h3⟩ := ih
        exact ⟨s₁, s₂, Relation.ReflTransGen.head hab h1, h2, h3⟩

/-! ## Multistep relations -/

/-- Filtering silent labels from a saturated multistep transition yields a
canonical `SMTr`. -/
theorem saturate_mTr_to_sMTr [DecidableEq Label]
    (h : lts.saturate.MTr s μs t) :
    lts.SMTr s (μs.filter (fun μ => μ ≠ _root_.Cslib.HasTau.τ)) t := by
  induction μs generalizing s t with
  | nil =>
      have heq : s = t := by simpa using h
      subst t
      exact _root_.Cslib.LTS.SMTr.refl _ _
  | cons label labels ih =>
      rw [_root_.Cslib.LTS.MTr.cons_iff] at h
      obtain ⟨middle, head, tail⟩ := h
      have ih' : lts.SMTr middle (labels.filter (fun μ => μ ≠ _root_.Cslib.HasTau.τ)) t :=
        ih tail
      by_cases hlabel : label = _root_.Cslib.HasTau.τ
      · subst hlabel
        simp only [List.filter_cons, decide_eq_false (not_ne_iff.mpr rfl),
          Bool.false_eq_true, ite_false]
        exact (_root_.Cslib.LTS.SMTr.τ head).comp ih'
      · simp only [List.filter_cons, decide_eq_true hlabel, ite_true]
        exact _root_.Cslib.LTS.SMTr.stepL head ih'

/-- Canonical `SMTr` lifts to a saturated multistep transition whose
visible-label filter agrees. -/
theorem sMTr_to_exists_saturate_mTr [DecidableEq Label]
    (h : lts.SMTr s μs t) :
    ∃ νs, lts.saturate.MTr s νs t ∧
      νs.filter (fun μ => μ ≠ _root_.Cslib.HasTau.τ) =
        μs.filter (fun μ => μ ≠ _root_.Cslib.HasTau.τ) := by
  induction h
  case τ hstep =>
    refine ⟨[_root_.Cslib.HasTau.τ],
      _root_.Cslib.LTS.MTr.stepL hstep _root_.Cslib.LTS.MTr.refl, ?_⟩
    simp
  case stepL s1 μ s2 μs s3 hstep hmstr ih =>
    obtain ⟨νs, hMTr, hfilter⟩ := ih
    refine ⟨μ :: νs,
      _root_.Cslib.LTS.MTr.stepL hstep hMTr, ?_⟩
    by_cases hμ : μ = _root_.Cslib.HasTau.τ
    · rw [List.filter_cons_of_neg (by simp [hμ]),
        List.filter_cons_of_neg (by simp [hμ]), hfilter]
    · rw [List.filter_cons_of_pos (by simp [hμ]),
        List.filter_cons_of_pos (by simp [hμ]), hfilter]

/-- Silent closure is canonical empty-list `SMTr`. -/
theorem tauSTr_iff_sMTr_nil :
    lts.τSTr s t ↔ lts.SMTr s [] t :=
  _root_.Cslib.LTS.sMTr_τSTr_iff

/-- Silent closure is a canonical multistep transition labelled only by `tau`. -/
theorem tauSTr_iff_exists_mTr_replicate :
    lts.τSTr s t ↔
      ∃ n, lts.MTr s (List.replicate n _root_.Cslib.HasTau.τ) t := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, _root_.Cslib.LTS.MTr.refl⟩
    | @head a b hab _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, _root_.Cslib.LTS.MTr.stepL hab hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero =>
        rw [List.replicate_zero] at hn
        have heq : s = t := by simpa using hn
        subst t
        exact .refl
    | succ n ih =>
        rw [List.replicate_succ] at hn
        obtain ⟨middle, head, tail⟩ := _root_.Cslib.LTS.MTr.cons_iff.mp hn
        exact Relation.ReflTransGen.head head (ih tail)

/-! ## Simulations -/

/-- Canonical simulation into the saturated system is simulation between
saturated systems. -/
theorem isSimulation_saturate_iff :
    _root_.Cslib.LTS.IsSimulation lts.saturate lts.saturate r ↔
      _root_.Cslib.LTS.IsSimulation lts lts.saturate r := by
  constructor
  · intro h
    exact h.mono lts.tr_le_tr_saturate le_rfl
  · intro h
    exact h.isSimulation_saturate_left

/-- Similarity into the saturated system is similarity between saturated
systems. -/
theorem similarity_saturate_iff :
    _root_.Cslib.LTS.Similarity lts lts.saturate s t ↔
      _root_.Cslib.LTS.Similarity lts.saturate lts.saturate s t := by
  constructor
  · rintro ⟨r, hrel, hsim⟩
    exact ⟨r, hrel, isSimulation_saturate_iff.mpr hsim⟩
  · rintro ⟨r, hrel, hsim⟩
    exact ⟨r, hrel, isSimulation_saturate_iff.mp hsim⟩

/-! ## Divergence and set closure -/

/-- Canonical divergence is an infinite run containing only the silent label.
This direction is constructive because every label is fixed to `tau`. -/
theorem divergent_iff_exists_tau_omegaRun :
    _root_.Cslib.LTS.Divergent lts s ↔
      ∃ ss : ℕ → State, ss 0 = s ∧
        ∀ i, lts.Tr (ss i) _root_.Cslib.HasTau.τ (ss (i + 1)) := by
  constructor
  · rintro ⟨ss, μs, hexec, h0, htrace⟩
    exact ⟨fun i => ss i, h0, fun i => by
      have h := hexec i
      rw [htrace i] at h
      exact h⟩
  · rintro ⟨ss, h0, hstep⟩
    exact ⟨⟨ss⟩, ⟨fun _ => _root_.Cslib.HasTau.τ⟩,
      fun i => hstep i, h0, fun _ => rfl⟩

/-- Membership in canonical silent closure is reachability by silent closure. -/
theorem mem_tauClosure_iff {S : Set State} :
    t ∈ lts.τClosure S ↔ ∃ s ∈ S, lts.τSTr s t := by
  constructor
  · intro h
    obtain ⟨s, hs, htr⟩ := (_root_.Cslib.LTS.mem_setImage).mp h
    exact ⟨s, hs, (_root_.Cslib.LTS.sTr_τSTr_iff _).mp htr⟩
  · rintro ⟨s, hs, hcl⟩
    exact (_root_.Cslib.LTS.mem_setImage).mpr ⟨s, hs,
      (_root_.Cslib.LTS.sTr_τSTr_iff _).mpr hcl⟩

end LTS

end Cslib.Semantics
