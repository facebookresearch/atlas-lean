/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.KernelBias
public import MathlibExt.Probability.Statistics.Nonparametric.KernelDensity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Positive case: box kernel at an interior point of a uniform density. -/
example : Tendsto (fun h : ℝ => ∫ u : ℝ, (if |u| ≤ (1 : ℝ) then (1 / 2 : ℝ) else 0)
    * (if (0 : ℝ) ≤ (1 / 2 : ℝ) - h * u ∧ (1 / 2 : ℝ) - h * u ≤ 1 then (1 : ℝ) else 0))
    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hf_meas : Measurable (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) := by
    have hEq : {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1} = Set.Icc 0 1 := rfl
    have hset : MeasurableSet {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1} := by
      rw [hEq]; exact measurableSet_Icc
    exact Measurable.ite hset measurable_const measurable_const
  have hf_nonneg : ∀ x, 0 ≤
      (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) x := by
    intro x
    show 0 ≤ (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
    by_cases h : (0:ℝ) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h]; norm_num
    · rw [ite_eq_right h]
  have hf_le : ∀ x, (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) x ≤ 1 := by
    intro x
    show (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) ≤ 1
    by_cases h : (0:ℝ) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; norm_num
  have hK0 : (fun u : ℝ => if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)
      = Set.indicator (Set.Icc (-1) 1) (fun _ => (1/2:ℝ)) := by
    funext u
    show (if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)
      = Set.indicator (Set.Icc (-1) 1) (fun _ => (1/2:ℝ)) u
    by_cases h : |u| ≤ (1:ℝ)
    · have hmem : u ∈ Set.Icc (-1:ℝ) 1 := by simpa [Set.mem_Icc, abs_le] using h
      rw [ite_eq_left h, Set.indicator_of_mem hmem (fun _ => (1/2:ℝ))]
    · have hmem : u ∉ Set.Icc (-1:ℝ) 1 := by simpa [Set.mem_Icc, abs_le] using h
      rw [ite_eq_right h, Set.indicator_of_notMem hmem (fun _ => (1/2:ℝ))]
  have hK_int : Integrable (fun u : ℝ => if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0) := by
    rw [hK0]
    have hIcc : MeasurableSet (Set.Icc (-1:ℝ) 1) := measurableSet_Icc
    rw [integrable_indicator_iff hIcc]
    have hfin : volume (Set.Icc (-1:ℝ) 1) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const hfin (by simp)
  have hK_one : (∫ u : ℝ, (if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)) = 1 := by
    rw [hK0, integral_indicator measurableSet_Icc, setIntegral_const]
    have hvol : volume.real (Set.Icc (-1:ℝ) 1) = 2 := by
      unfold Measure.real
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 - -1)]
      norm_num
    rw [hvol, smul_eq_mul]
    norm_num
  have hcont : ContinuousAt
      (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) (1/2) := by
    have hev : (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
        =ᶠ[𝓝 (1/2:ℝ)] fun _ => 1 := by
      have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝 (1/2:ℝ) :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with x hx
      show (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) = 1
      exact ite_eq_left ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact continuousAt_const.congr_of_eventuallyEq hev
  have hft : (if (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 then (1:ℝ) else 0) = 1 := by
    have hc : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 := by norm_num
    exact ite_eq_left hc
  have main := ProbabilityTheory.kde_bias_tends_to_zero
    (K := fun u : ℝ => if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)
    (f := fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
    (t := (1/2:ℝ)) (B := (1:ℝ))
    hf_meas hf_nonneg hf_le hK_int hK_one hcont
  rw [hft] at main
  exact main

/-- Boundary case: at fixed `h > 0` the bias need not vanish. With `f` the
indicator of `[0, 1]`, `K` the box kernel and `t = 0`, the expectation at `h = 1`
is `1 / 2`, not `f 0 = 1`. -/
example : (∫ u : ℝ, (if |u| ≤ (1 : ℝ) then (1 / 2 : ℝ) else 0)
    * (if (0 : ℝ) ≤ (0 : ℝ) - 1 * u ∧ (0 : ℝ) - 1 * u ≤ 1 then (1 : ℝ) else 0))
    ≠ (1 : ℝ) := by
  have hint : (fun u : ℝ => (if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)
        * (if (0:ℝ) ≤ (0:ℝ) - 1 * u ∧ (0:ℝ) - 1 * u ≤ 1 then (1:ℝ) else 0))
      = Set.indicator (Set.Icc (-1) 0) (fun _ => (1/2:ℝ)) := by
    funext u
    show (if |u| ≤ (1:ℝ) then (1/2:ℝ) else 0)
          * (if (0:ℝ) ≤ (0:ℝ) - 1 * u ∧ (0:ℝ) - 1 * u ≤ 1 then (1:ℝ) else 0)
        = Set.indicator (Set.Icc (-1) 0) (fun _ => (1/2:ℝ)) u
    by_cases h1 : |u| ≤ (1:ℝ)
    · by_cases h2 : (0:ℝ) ≤ (0:ℝ) - 1 * u ∧ (0:ℝ) - 1 * u ≤ 1
      · have hmem : u ∈ Set.Icc (-1:ℝ) 0 := by
          simp only [Set.mem_Icc]
          constructor <;> linarith [h2.1, h2.2]
        rw [ite_eq_left h1, ite_eq_left h2,
          Set.indicator_of_mem hmem (fun _ => (1/2:ℝ))]
        simp
      · have hmem : u ∉ Set.Icc (-1:ℝ) 0 := by
          intro hcon
          simp only [Set.mem_Icc] at hcon
          apply h2
          constructor <;> linarith [hcon.1, hcon.2]
        rw [ite_eq_left h1, ite_eq_right h2,
          Set.indicator_of_notMem hmem (fun _ => (1/2:ℝ))]
        simp
    · have hmem : u ∉ Set.Icc (-1:ℝ) 0 := by
        intro hcon
        simp only [Set.mem_Icc] at hcon
        apply h1
        rw [abs_le]
        constructor <;> linarith [hcon.1, hcon.2]
      rw [ite_eq_right h1, Set.indicator_of_notMem hmem (fun _ => (1/2:ℝ))]
      simp
  rw [hint, integral_indicator measurableSet_Icc, setIntegral_const]
  have hvol : volume.real (Set.Icc (-1:ℝ) 0) = 1 := by
    unfold Measure.real
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 0 - -1)]
    norm_num
  rw [hvol, smul_eq_mul]
  norm_num

/-- Degenerate case: the bias-limit conclusion is false for the zero kernel
when `f t ≠ 0`, so the `∫ K = 1` hypothesis is load-bearing. -/
example {f : ℝ → ℝ} {t : ℝ} (hft : f t ≠ 0)
    (hlim : Tendsto (fun h : ℝ => ∫ u : ℝ, (0 : ℝ) * f (t - h * u))
      (𝓝[>] (0 : ℝ)) (𝓝 (f t))) : False := by
  have hzero : (fun h : ℝ => ∫ u : ℝ, (0:ℝ) * f (t - h * u)) = fun _ => (0:ℝ) := by
    funext h
    simp
  rw [hzero] at hlim
  have heq : f t = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  exact hft heq

/-- Focused case: the expectation corollary fires with the same hypotheses. -/
example {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hcont : ContinuousAt f t)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P) :
    Tendsto (fun h : ℝ => ∫ ω, ProbabilityTheory.kde K h (fun i => X i ω) t ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 (f t)) :=
  ProbabilityTheory.kde_expectation_tendsto hf_meas hf_nonneg hf_le hK_meas hK_int
    hK_one hcont hn hX

/-- Noncompact case: a Gaussian-shaped kernel satisfies the hypotheses with no
compact-support assumption. -/
example : Tendsto (fun h : ℝ => ∫ u : ℝ, ((Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp ((-(1/2) : ℝ) * u ^ 2))
      * (if (0:ℝ) ≤ (1/2:ℝ) - h * u ∧ (1/2:ℝ) - h * u ≤ 1 then (1:ℝ) else 0))
    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hf_meas : Measurable (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) := by
    have hEq : {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1} = Set.Icc 0 1 := rfl
    have hset : MeasurableSet {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1} := by
      rw [hEq]; exact measurableSet_Icc
    exact Measurable.ite hset measurable_const measurable_const
  have hf_nonneg : ∀ x, 0 ≤
      (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) x := by
    intro x
    show 0 ≤ (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
    by_cases h : (0:ℝ) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h]; norm_num
    · rw [ite_eq_right h]
  have hf_le : ∀ x, (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) x ≤ 1 := by
    intro x
    show (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) ≤ 1
    by_cases h : (0:ℝ) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; norm_num
  have hcont : ContinuousAt
      (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) (1/2) := by
    have hev : (fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
        =ᶠ[𝓝 (1/2:ℝ)] fun _ => 1 := by
      have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝 (1/2:ℝ) :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with x hx
      show (if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0) = 1
      exact ite_eq_left ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact continuousAt_const.congr_of_eventuallyEq hev
  have hft : (if (0:ℝ) ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ 1 then (1:ℝ) else 0) = 1 := by
    have hc : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 := by norm_num
    exact ite_eq_left hc
  have hK_int : Integrable (fun u : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp ((-(1/2):ℝ) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _
  have hK_one : (∫ u : ℝ, (Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp ((-(1/2):ℝ) * u ^ 2)) = 1 := by
    rw [integral_const_mul, integral_gaussian (1/2 : ℝ)]
    have h2 : Real.pi / (1/2 : ℝ) = 2 * Real.pi := by
      rw [div_eq_iff (by norm_num : (1/2 : ℝ) ≠ 0)]; ring
    rw [h2]
    exact inv_mul_cancel₀ (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)
  have hmain := ProbabilityTheory.kde_bias_tends_to_zero
    (K := fun u : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((-(1/2):ℝ) * u ^ 2))
    (f := fun x : ℝ => if (0:ℝ) ≤ x ∧ x ≤ 1 then (1:ℝ) else 0)
    (t := (1/2:ℝ)) (B := (1:ℝ))
    hf_meas hf_nonneg hf_le hK_int hK_one hcont
  rw [hft] at hmain
  exact hmain
