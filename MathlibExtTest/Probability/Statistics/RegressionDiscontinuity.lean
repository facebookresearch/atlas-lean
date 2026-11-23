/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.RegressionDiscontinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tests for sharp regression-discontinuity identification

Forcing variable uniform on `[0, 1]` (Lebesgue measure restricted to `[0, 1]`), cutoff `1/2`,
potential outcomes `Y₀ = x` and `Y₁ = x + 1`. Every hypothesis of `sharpRD_identification` is
discharged for the version `sharpRDMean`, giving a jump of `3/2 - 1/2 = 1`, the cutoff effect;
the same conclusion follows for a second version that differs from it on the null set `{1/2}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.RegressionDiscontinuity

namespace MathlibExtTest.Probability.Statistics.RegressionDiscontinuity

/-- Test 1a: `Y₀ = id` is `σ(id)`-measurable, so its conditional expectation is itself. -/
theorem condExp_Y0_test :
    (volume.restrict (Set.Icc (0 : ℝ) 1))[(id : ℝ → ℝ) | MeasurableSpace.comap (id : ℝ → ℝ) inferInstance]
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (id : ℝ → ℝ) ∘ (id : ℝ → ℝ) := by
  rw [MeasurableSpace.comap_id]
  have h_int : Integrable (id : ℝ → ℝ) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    continuous_id.integrableOn_Icc
  have h_ce := MeasureTheory.condExp_of_stronglyMeasurable (m := (inferInstance : MeasurableSpace ℝ))
    (m₀ := inferInstance) (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (le_rfl) stronglyMeasurable_id h_int
  simp only [Function.comp_id] at h_ce ⊢
  rw [h_ce]

/-- Test 1b: `Y₁ = fun x => x + 1` is `σ(id)`-measurable. -/
theorem condExp_Y1_test :
    (volume.restrict (Set.Icc (0 : ℝ) 1))[(fun x : ℝ => x + 1) | MeasurableSpace.comap (id : ℝ → ℝ) inferInstance]
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x : ℝ => x + 1) ∘ (id : ℝ → ℝ) := by
  rw [MeasurableSpace.comap_id]
  have h_cont : Continuous (fun x : ℝ => x + 1) := continuous_id.add continuous_const
  have h_int : Integrable (fun x : ℝ => x + 1) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    h_cont.integrableOn_Icc
  have h_ce := MeasureTheory.condExp_of_stronglyMeasurable (m := (inferInstance : MeasurableSpace ℝ))
    (m₀ := inferInstance) (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (le_rfl) h_cont.stronglyMeasurable h_int
  have h_comp : (fun x : ℝ => x + 1) ∘ (id : ℝ → ℝ) = (fun x : ℝ => x + 1) := rfl
  rw [h_comp, h_ce]

/-- Test 1c: right one-sided support at `c = 1/2`. -/
theorem suppR_test : ∀ ε > 0, (volume.restrict (Set.Icc (0 : ℝ) 1))
    ((id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2 : ℝ) (1/2 + ε)) ≠ 0 := by
  intro ε hε
  rw [Set.preimage_id, Measure.restrict_apply measurableSet_Ioo]
  set δ : ℝ := min ε (1/2 : ℝ) with hδ
  have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨hε, by norm_num⟩
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_half : δ ≤ 1/2 := min_le_right _ _
  have h_sub : Set.Ioo (1/2 : ℝ) (1/2 + δ)
      ⊆ Set.Ioo (1/2 : ℝ) (1/2 + ε) ∩ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Icc] at hx ⊢
    refine ⟨⟨hx.1, ?_⟩, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  have h_pos : volume (Set.Ioo (1/2 : ℝ) (1/2 + δ)) ≠ 0 := by
    rw [Real.volume_Ioo]
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    have h_eq : (1/2 + δ - 1/2 : ℝ) = δ := by ring
    rw [h_eq]
    exact not_le_of_gt hδ_pos
  exact fun h0 => h_pos (measure_mono_null h_sub h0)

/-- Test 1d: left one-sided support at `c = 1/2`. -/
theorem suppL_test : ∀ ε > 0, (volume.restrict (Set.Icc (0 : ℝ) 1))
    ((id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2 - ε : ℝ) (1/2 : ℝ)) ≠ 0 := by
  intro ε hε
  rw [Set.preimage_id, Measure.restrict_apply measurableSet_Ioo]
  set δ : ℝ := min ε (1/2 : ℝ) with hδ
  have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨hε, by norm_num⟩
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_half : δ ≤ 1/2 := min_le_right _ _
  have h_sub : Set.Ioo (1/2 - δ : ℝ) (1/2 : ℝ)
      ⊆ Set.Ioo (1/2 - ε : ℝ) (1/2 : ℝ) ∩ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Icc] at hx ⊢
    refine ⟨⟨?_, hx.2⟩, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  have h_pos : volume (Set.Ioo (1/2 - δ : ℝ) (1/2 : ℝ)) ≠ 0 := by
    rw [Real.volume_Ioo]
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    have h_eq : (1/2 - (1/2 - δ) : ℝ) = δ := by ring
    rw [h_eq]
    exact not_le_of_gt hδ_pos
  exact fun h0 => h_pos (measure_mono_null h_sub h0)

/-- Test 2a: hypothesis-discharge probe via `sharpRD_identification` with `r = sharpRDMean`. -/
theorem hypothesis_discharge_test :
    (3/2 : ℝ) - 1/2 = (fun x : ℝ => x + 1) (1/2 : ℝ) - (id : ℝ → ℝ) (1/2 : ℝ) := by
  have hX : Measurable (id : ℝ → ℝ) := measurable_id
  have hY₀ : Integrable (id : ℝ → ℝ) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    continuous_id.integrableOn_Icc
  have hY₁ : Integrable (fun x : ℝ => x + 1) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (continuous_id.add continuous_const).integrableOn_Icc
  have h₀ := condExp_Y0_test
  have h₁ := condExp_Y1_test
  have hc₀ : ContinuousAt (id : ℝ → ℝ) (1/2 : ℝ) := continuousAt_id
  have hc₁ : ContinuousAt (fun x : ℝ => x + 1) (1/2 : ℝ) :=
    continuousAt_id.add continuousAt_const
  have hsuppR := suppR_test
  have hsuppL := suppL_test
  have hver := condExp_observed_ae_eq_sharpRDMean hX (1/2 : ℝ) hY₀ hY₁ h₀ h₁
  have h2 := tendsto_sharpRDMean (c := (1/2 : ℝ)) (m₀ := (id : ℝ → ℝ))
    (m₁ := (fun x : ℝ => x + 1)) hc₀ hc₁
  have h_eq1 : (1/2 : ℝ) + 1 = (3/2 : ℝ) := by norm_num
  have hLr : Tendsto (sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1))
      (𝓝[>] (1/2 : ℝ)) (𝓝 (3/2 : ℝ)) := by
    have h := h2.1
    rw [h_eq1] at h
    exact h
  have hLl : Tendsto (sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (1/2 : ℝ)) := by
    have h := h2.2
    -- `id (1/2) = 1/2` definitionally
    simpa using h
  exact sharpRD_identification hX hY₀ hY₁ h₀ h₁ hc₀ hc₁ hsuppR hsuppL hver hLr hLl

/-- Test 2b: the cutoff effect equals `1`. -/
theorem hypothesis_discharge_value_test :
    (fun x : ℝ => x + 1) (1/2 : ℝ) - (id : ℝ → ℝ) (1/2 : ℝ) = 1 := by
  norm_num

/-- Test 3: version-independence probe with `r'` changed on the null set `{1/2}`. -/
theorem version_independence_test :
    (3/2 : ℝ) - 1/2 = (fun x : ℝ => x + 1) (1/2 : ℝ) - (id : ℝ → ℝ) (1/2 : ℝ) := by
  classical
  have hX : Measurable (id : ℝ → ℝ) := measurable_id
  have hY₀ : Integrable (id : ℝ → ℝ) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    continuous_id.integrableOn_Icc
  have hY₁ : Integrable (fun x : ℝ => x + 1) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (continuous_id.add continuous_const).integrableOn_Icc
  have h₀ := condExp_Y0_test
  have h₁ := condExp_Y1_test
  have hc₀ : ContinuousAt (id : ℝ → ℝ) (1/2 : ℝ) := continuousAt_id
  have hc₁ : ContinuousAt (fun x : ℝ => x + 1) (1/2 : ℝ) :=
    continuousAt_id.add continuousAt_const
  have hsuppR := suppR_test
  have hsuppL := suppL_test
  have h_obs := condExp_observed_ae_eq_sharpRDMean hX (1/2 : ℝ) hY₀ hY₁ h₀ h₁
  -- `{1/2}` is null for `volume.restrict (Icc 0 1)`
  have h_single : (volume.restrict (Set.Icc (0 : ℝ) 1)) {(1/2 : ℝ)} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton (1/2 : ℝ))]
    exact measure_mono_null (Set.inter_subset_left) Real.volume_singleton
  have h_ae_ne : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), x ∉ {(1/2 : ℝ)} :=
    measure_eq_zero_iff_ae_notMem.mp h_single
  -- `r' ∘ id =ᵐ sharpRDMean ∘ id`
  have h_eq_ae : (fun x : ℝ => if x = 1/2 then (100 : ℝ)
      else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x) ∘ (id : ℝ → ℝ)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) ∘ (id : ℝ → ℝ) := by
    filter_upwards [h_ae_ne] with x hx
    simp only [Function.comp_apply, id_eq] at hx ⊢
    have hne : x ≠ (1/2 : ℝ) := fun h => hx (Set.mem_singleton_iff.mpr h)
    simp only [ite_eq_right hne]
  have hver : (volume.restrict (Set.Icc (0 : ℝ) 1))[observed
      ((id : ℝ → ℝ) ⁻¹' Set.Ici (1/2 : ℝ)) (id : ℝ → ℝ) (fun x : ℝ => x + 1)
      | MeasurableSpace.comap (id : ℝ → ℝ) inferInstance]
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x : ℝ => if x = 1/2 then (100 : ℝ)
        else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x)
      ∘ (id : ℝ → ℝ) :=
    h_obs.trans h_eq_ae.symm
  -- one-sided limits of `r'`
  have h2 := tendsto_sharpRDMean (c := (1/2 : ℝ)) (m₀ := (id : ℝ → ℝ))
    (m₁ := (fun x : ℝ => x + 1)) hc₀ hc₁
  have h_eq1 : (1/2 : ℝ) + 1 = (3/2 : ℝ) := by norm_num
  have h_limR : Tendsto (sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1))
      (𝓝[>] (1/2 : ℝ)) (𝓝 (3/2 : ℝ)) := by
    have h := h2.1
    rw [h_eq1] at h
    exact h
  have h_limL : Tendsto (sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (1/2 : ℝ)) := by
    have h := h2.2
    simpa using h
  have h_eqR : (fun x : ℝ => if x = 1/2 then (100 : ℝ)
        else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x)
      =ᶠ[𝓝[>] (1/2 : ℝ)] sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x ≠ (1/2 : ℝ) := ne_of_gt hx
    simp only [ite_eq_right hne]
  have h_eqL : (fun x : ℝ => if x = 1/2 then (100 : ℝ)
        else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x)
      =ᶠ[𝓝[<] (1/2 : ℝ)] sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x ≠ (1/2 : ℝ) := ne_of_lt hx
    simp only [ite_eq_right hne]
  have hLr_clean : Tendsto (fun x : ℝ => if x = 1/2 then (100 : ℝ)
        else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x)
      (𝓝[>] (1/2 : ℝ)) (𝓝 (3/2 : ℝ)) :=
    Filter.Tendsto.congr' h_eqR.symm h_limR
  have hLl_clean : Tendsto (fun x : ℝ => if x = 1/2 then (100 : ℝ)
        else sharpRDMean (1/2 : ℝ) (id : ℝ → ℝ) (fun x : ℝ => x + 1) x)
      (𝓝[<] (1/2 : ℝ)) (𝓝 (1/2 : ℝ)) :=
    Filter.Tendsto.congr' h_eqL.symm h_limL
  exact sharpRD_identification hX hY₀ hY₁ h₀ h₁ hc₀ hc₁ hsuppR hsuppL hver
    hLr_clean hLl_clean

end MathlibExtTest.Probability.Statistics.RegressionDiscontinuity
