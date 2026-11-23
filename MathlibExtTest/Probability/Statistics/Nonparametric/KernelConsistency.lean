/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.KernelConsistency
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Tests for mean-squared-error consistency of the kernel density estimator

* `kde_mse_tends_to_zero_rpow_bandwidth`: the bandwidth `h_N = (N + 1) ^ (-1/5)` meets the
  bandwidth hypotheses of `kde_mse_tends_to_zero`.
* `kde_mse_tends_to_zero_uniform_box`: the uniform density on `[0, 1]` with the box kernel on
  `[-1/2, 1/2]`, at the interior point `1/2`.
* `kde_bandwidth_inv_sq_not_rate`: `h_N = 1 / (N + 1)²` violates the rate hypothesis
  `(N + 1) h_N → ∞`.
* `kde_bandwidth_const_not_tendsto_zero`: a constant bandwidth `h_N = c > 0` violates
  `h_N → 0`.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Positive case: the bandwidth `h_N = (N + 1) ^ (-1/5)` meets the three bandwidth hypotheses,
so the MSE of any admissible kernel and density vanishes along it. -/
theorem kde_mse_tends_to_zero_rpow_bandwidth {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hK_sq : Integrable fun u => K u ^ 2)
    (hcont : ContinuousAt f t)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    (hindep : iIndepFun X P) :
    Tendsto (fun N : ℕ => ∫ ω, (kde K (((N + 1 : ℕ) : ℝ) ^ (-(1 / 5 : ℝ)))
      (fun i : Fin (N + 1) => X i ω) t - f t) ^ 2 ∂P) atTop (𝓝 0) := by
  have hbase : ∀ N : ℕ, (0 : ℝ) < ((N + 1 : ℕ) : ℝ) :=
    fun N => Nat.cast_pos.mpr (Nat.succ_pos N)
  have htop : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hh_pos : ∀ N : ℕ, 0 < (((N + 1 : ℕ) : ℝ) ^ (-(1 / 5 : ℝ))) :=
    fun N => Real.rpow_pos_of_pos (hbase N) _
  have hh_lim : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-(1 / 5 : ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp htop
  have hrate : (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * ((((N + 1 : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))))
      = fun N : ℕ => (((N + 1 : ℕ) : ℝ)) ^ ((4 / 5 : ℝ)) := by
    funext N
    have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := hbase N
    have e1 := Real.rpow_add hx (1 : ℝ) (-(1 / 5 : ℝ))
    rw [Real.rpow_one] at e1
    rw [← e1]
    congr 1
    norm_num
  have hh_n : Tendsto
      (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * ((((N + 1 : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))))
      atTop atTop := by
    rw [hrate]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp htop
  exact kde_mse_tends_to_zero hf_meas hf_nonneg hf_le hK_meas hK_int hK_one hK_sq
    hcont hh_pos hh_lim hh_n hX hindep

/-- Toy case: the uniform density on `[0, 1]` (locally constant near `1/2`) with the box
kernel on `[-1/2, 1/2]`; the MSE at the interior point `1/2` vanishes. -/
theorem kde_mse_tends_to_zero_uniform_box {hh : ℕ → ℝ}
    (hh_pos : ∀ N, 0 < hh N) (hh_lim : Tendsto hh atTop (𝓝 0))
    (hh_n : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * hh N) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x =>
      ENNReal.ofReal ((Set.Icc (0 : ℝ) 1).indicator 1 x)) P)
    (hindep : iIndepFun X P) :
    Tendsto (fun N : ℕ => ∫ ω, (kde ((Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator 1) (hh N)
      (fun i : Fin (N + 1) => X i ω) (1 / 2) - 1) ^ 2 ∂P) atTop (𝓝 0) := by
  have hf_meas : Measurable ((Set.Icc (0:ℝ) 1).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  have hf_nonneg : ∀ x, 0 ≤ (Set.Icc (0:ℝ) 1).indicator (1 : ℝ → ℝ) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx 1]
      exact zero_le_one
    · rw [Set.indicator_of_notMem hx 1]
  have hf_le : ∀ x, (Set.Icc (0:ℝ) 1).indicator (1 : ℝ → ℝ) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx 1]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx 1]
      exact zero_le_one
  have hK_meas : Measurable ((Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  have hK_int : Integrable ((Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    have hfin : volume (Set.Icc (-(1/2):ℝ) (1/2)) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hC : ‖(1:ℝ)‖ₑ ≠ ∞ := by simp
    exact integrableOn_const hfin hC
  have hK_one : (∫ u, (Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ) u) = 1 := by
    rw [integral_indicator measurableSet_Icc]
    simp only [Pi.one_apply]
    rw [setIntegral_const]
    have hvol : volume.real (Set.Icc (-(1/2):ℝ) (1/2)) = 1 := by
      unfold Measure.real
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1/2:ℝ) - -(1/2))]
      norm_num
    rw [hvol, smul_eq_mul]
    norm_num
  have hK_sq : Integrable
      (fun u => ((Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ) u) ^ 2) := by
    have heq : (fun u => ((Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ) u) ^ 2)
        = (Set.Icc (-(1/2):ℝ) (1/2)).indicator (1 : ℝ → ℝ) := by
      funext u
      by_cases hu : u ∈ Set.Icc (-(1/2):ℝ) (1/2)
      · rw [Set.indicator_of_mem hu 1, Pi.one_apply, one_pow]
      · rw [Set.indicator_of_notMem hu 1]
        norm_num
    rw [heq]
    exact hK_int
  have hcont : ContinuousAt ((Set.Icc (0:ℝ) 1).indicator (1 : ℝ → ℝ)) (1/2) := by
    have hev : (Set.Icc (0:ℝ) 1).indicator (1 : ℝ → ℝ) =ᶠ[𝓝 (1/2:ℝ)] fun _ => 1 := by
      have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝 (1/2:ℝ) :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with x hx
      have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      rw [Set.indicator_of_mem hxI 1]
      rfl
    exact continuousAt_const.congr_of_eventuallyEq hev
  have hf12 : (Set.Icc (0:ℝ) 1).indicator (1:ℝ→ℝ) (1/2) = 1 := by
    rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) 1]
    rfl
  have hmain := kde_mse_tends_to_zero hf_meas hf_nonneg hf_le hK_meas hK_int hK_one
    hK_sq hcont hh_pos hh_lim hh_n hX hindep
  rw [hf12] at hmain
  exact hmain

/-- Excluded shape `n h_n → 0`: `h_N = 1 / (N + 1)²` gives `(N + 1) h_N = 1 / (N + 1) → 0`, so
the rate hypothesis `hh_n` of `kde_mse_tends_to_zero` fails for it. -/
theorem kde_bandwidth_inv_sq_not_rate :
    ¬ Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * (1 / ((N + 1 : ℕ) : ℝ) ^ 2)) atTop atTop := by
  have e : (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * (1 / ((N + 1 : ℕ) : ℝ) ^ 2))
      = fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹ := by
    funext N
    have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.succ_pos N)).ne'
    field_simp
  have hNtop : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * (1 / ((N + 1 : ℕ) : ℝ) ^ 2))
      atTop (𝓝 0) := by
    rw [e]
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hNtop
  exact not_tendsto_atTop_of_tendsto_nhds h0

/-- Excluded shape: a constant bandwidth `h_N = c > 0` does not tend to `0`, so the hypothesis
`hh_lim` of `kde_mse_tends_to_zero` fails for it. -/
theorem kde_bandwidth_const_not_tendsto_zero {c : ℝ} (hc : 0 < c) :
    ¬ Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
  intro h
  have h2 := tendsto_nhds_unique h tendsto_const_nhds
  linarith

end ProbabilityTheory
