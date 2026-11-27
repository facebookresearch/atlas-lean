/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UrysohnsLemma

/-!
# Compact-local Radon approximation of vector-valued Lp functions

The regular measure and a compact-local cutoff supply continuous compact-support
approximations in arbitrary real normed targets. The proof needs no global normal
space, countability, separability or sigma-finiteness assumption. These are the
original complete approximation proofs used by normalized Haar right translation,
now exposed for the actual Haar L2 compact-support completion constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

noncomputable section

universe uG uH

/-- Let `X` be a locally compact R₁ topological space with its Borel σ-algebra, let `ν` be a regular
measure, and let `E` be a normed real vector space. The extended exponent `p` is finite, and the
approximation tolerance `ε` is nonzero. The approximated set is compact and closed, and its
indicator has the specified constant value in `E`.

A compact-local cutoff approximates a constant vector on an compact set. -/
theorem compactIndicatorApprox
    {X : Type uG} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.Regular]
    {E : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ENNReal} (hp : p ≠ ⊤) {s : Set X} (hs : IsCompact s) (hsclosed : IsClosed s)
    (c : E) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ f : X → E, HasCompactSupport f ∧ Continuous f ∧ MemLp f p ν ∧
      eLpNorm (f - s.indicator (fun _ => c)) p ν ≤ ε := by
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ≥0, 0 < η ∧ ∀ t : Set X,
      ν t ≤ η → NullMeasurableSet t ν → eLpNorm (t.indicator fun _ => c) p ν ≤ ε :=
    exists_eLpNorm_indicator_le hp c hε
  obtain ⟨V, hsV, hVopen, hνV, hdiff⟩ : ∃ V : Set X,
      V ⊇ s ∧ IsOpen V ∧ ν V < ⊤ ∧ ν (V \ s) < η :=
    hsclosed.measurableSet.exists_isOpen_sdiff_lt hs.measure_ne_top
      (ENNReal.coe_pos.mpr hηpos).ne'
  obtain ⟨ψ, hψs, hψcompact, hψsupport, hψrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hs hVopen hsV
  have hψout (x : X) (hx : x ∉ V) : ψ x = 0 := by
    by_contra hne
    exact hx (hψsupport (subset_tsupport ψ hne))
  have hψnorm (x : X) : ‖ψ x‖ = ψ x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hψrange x).1]
  have hbound (x : X) : ‖ψ x • c‖ ≤ ‖c‖ := by
    rw [norm_smul, hψnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψrange x).2
  have hψmem : MemLp (ψ : X → ℝ) p ν := by
    have hV : eLpNorm (V.indicator fun _ : X => (1 : ℝ)) p ν < ⊤ :=
      (eLpNorm_indicator_const_le _ _ hVopen.measurableSet.nullMeasurableSet).trans_lt
        (by simp [lt_top_iff_ne_top, hνV.ne])
    refine (eLpNorm_mono ψ.continuous.aestronglyMeasurable ?_).trans_lt hV
    intro x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (hψrange x).1, norm_one]
      exact (hψrange x).2
    · simp only [hψout x hx, Set.indicator_of_notMem hx, Real.norm_eq_abs, abs_zero]
      exact le_rfl
  have hmem : MemLp (fun x : X => ψ x • c) p ν :=
    MemLp.smul hψmem (memLp_top_const c) (p := p) (q := ⊤)
  have hpoint (x : X) :
      ‖ψ x • c - s.indicator (fun _ => c) x‖ ≤ ‖(V \ s).indicator (fun _ => c) x‖ := by
    by_cases hxs : x ∈ s
    · have hψone : ψ x = (1 : ℝ) := by
        simpa only [Pi.one_apply] using hψs hxs
      rw [Set.indicator_of_mem hxs, hψone, one_smul, sub_self, norm_zero]
      exact norm_nonneg _
    · by_cases hxV : x ∈ V
      · simpa only [Set.indicator_of_notMem hxs, sub_zero,
          Set.indicator_of_mem (show x ∈ V \ s from ⟨hxV, hxs⟩)] using hbound x
      · simp only [hψout x hxV, zero_smul, Set.indicator_of_notMem hxs, sub_zero,
          norm_zero, Set.indicator_of_notMem (show x ∉ V \ s from fun hx => hxV hx.1)]
        exact le_rfl
  refine ⟨fun x => ψ x • c,
    (show HasCompactSupport (ψ : X → ℝ) from hψcompact).smul_right,
    ψ.continuous.smul continuous_const, hmem, ?_⟩
  exact (eLpNorm_mono (hmem.aestronglyMeasurable.sub
    (aestronglyMeasurable_const.indicator hsclosed.measurableSet)) hpoint).trans
      (hη _ hdiff.le (hVopen.measurableSet.diff hsclosed.measurableSet).nullMeasurableSet)

/-- Let `X` be a locally compact R₁ topological space with its Borel σ-algebra, let `ν` be a regular
measure, and let `E` be a normed real vector space. The extended exponent `p` is finite, and the
approximation tolerance `ε` is nonzero. The function to be approximated belongs to `Lᵖ(ν;E)`.

Every Lp vector has a continuous compact-support approximation for a regular measure. -/
theorem locallyCompactVectorApprox
    {X : Type uG} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.Regular]
    {E : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ENNReal} (hp : p ≠ ⊤) {f : X → E} (hf : MemLp f p ν)
    {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ g : X → E, HasCompactSupport g ∧ eLpNorm (f - g) p ν ≤ ε ∧
      Continuous g ∧ MemLp g p ν := by
  suffices h : ∃ g : X → E, eLpNorm (f - g) p ν ≤ ε ∧ Continuous g ∧
      MemLp g p ν ∧ HasCompactSupport g by
    obtain ⟨g, hnorm, hcont, hmem, hcomp⟩ := h
    exact ⟨g, hcomp, hnorm, hcont, hmem⟩
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  · rintro f g ⟨hfcont, hfmem, hfcomp⟩ ⟨hgcont, hgmem, hgcomp⟩
    exact ⟨hfcont.add hgcont, hfmem.add hgmem, hfcomp.add hgcomp⟩
  intro c t ht htν δ hδ
  obtain ⟨σ, hσpos, hσ⟩ := exists_Lp_half E ν p hδ
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set X,
      ν s ≤ η → NullMeasurableSet s ν → eLpNorm (s.indicator fun _ => c) p ν ≤ σ :=
    exists_eLpNorm_indicator_le hp c hσpos.ne'
  obtain ⟨s, hst, hscompact, hsclosed, hνdiff⟩ :
      ∃ s : Set X, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ ν (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htν.ne (ENNReal.coe_pos.mpr hηpos).ne'
  have hI₁ : eLpNorm ((s.indicator fun _ => c) - t.indicator fun _ => c) p ν ≤ σ := by
    rw [← eLpNorm_neg, neg_sub, ← Set.indicator_sdiff hst]
    exact hη _ hνdiff.le (ht.diff hsclosed.measurableSet).nullMeasurableSet
  obtain ⟨g, hgcomp, hgcont, hgmem, hI₂⟩ :=
    compactIndicatorApprox ν hp hscompact hsclosed c hσpos.ne'
  have hI₃ : eLpNorm (g - t.indicator fun _ => c) p ν ≤ δ := by
    convert (hσ _ _ hI₂ hI₁).le using 2
    ext x
    simp
  exact ⟨g, hI₃, hgcont, hgmem, hgcomp⟩

end

end MeasureTheory
