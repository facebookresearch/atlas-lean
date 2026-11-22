/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.KernelBias
import MathlibExt.Probability.Statistics.EstimationRisk

/-!
# Mean-squared-error consistency of the kernel density estimator

This file splits the mean squared error of the kernel density estimator `kde` at a point `t`
into squared bias and variance, and shows that it tends to zero when the bandwidth shrinks
slowly enough relative to the sample size.

* `ProbabilityTheory.kde_mse_eq_bias_sq_add_variance`: for a bounded measurable kernel and a
  sample whose coordinates have a nonnegative, measurable density `f`, at every fixed `n`, `h`
  and `t`, `E[(f̂_h(t) - f(t))²] = (E[f̂_h(t)] - f(t))² + Var(f̂_h(t))`.
* `ProbabilityTheory.kde_mse_tends_to_zero`: at a continuity point `t` of a bounded,
  nonnegative, measurable density `f`, for an integrable measurable kernel with `∫ K = 1` and
  `∫ K² < ∞`, independent samples with density `f`, and bandwidths `h_N > 0` with `h_N → 0`
  and `(N + 1) h_N → ∞`, the mean squared error of the estimator built from the first `N + 1`
  samples tends to `0`.

Both splits are the generic estimator identity
`EstimationRisk.meanSquaredError_eq_variance_add_sq_expectation_sub` applied to `kde`. The
squared bias vanishes by `integral_kde_eq` and `kernel_smoothing_tendsto`, the variance by
`variance_kde_le`.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

open MathlibExt.Probability.Statistics.EstimationRisk in
/-- A KDE with a finite second moment has mean squared error at `θ` equal to squared bias plus
variance: `meanSquaredError_eq_variance_add_sq_expectation_sub` with `P` packaged as a
`ProbabilityMeasure`. -/
private lemma kde_mse_eq_of_memLp {K : ℝ → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {h t θ : ℝ}
    (hY : MemLp (fun ω => kde K h (fun i => X i ω) t) 2 P) :
    ∫ ω, (kde K h (fun i => X i ω) t - θ) ^ 2 ∂P
      = ((∫ ω, kde K h (fun i => X i ω) t ∂P) - θ) ^ 2
        + Var[fun ω => kde K h (fun i => X i ω) t; P] := by
  have hmse := meanSquaredError_eq_variance_add_sq_expectation_sub
    (μ := ⟨P, inferInstance⟩) (θ := θ) hY
  unfold meanSquaredError at hmse
  rw [add_comm]
  exact hmse

/-- **Bias-variance decomposition of the KDE mean squared error** at a fixed sample size `n`,
bandwidth `h` and point `t`: for a bounded measurable kernel and a nonnegative, measurable
density `f`, `E[(f̂_h(t) - f(t))²] = (E[f̂_h(t)] - f(t))² + Var(f̂_h(t))`. -/
theorem kde_mse_eq_bias_sq_add_variance {K f : ℝ → ℝ}
    (_hf_meas : Measurable f) (_hf_nonneg : ∀ x, 0 ≤ f x)
    (hK_meas : Measurable K) (hK_bdd : ∃ C, ∀ u, |K u| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    (h t : ℝ) :
    ∫ ω, (kde K h (fun i => X i ω) t - f t) ^ 2 ∂P
      = ((∫ ω, kde K h (fun i => X i ω) t ∂P) - f t) ^ 2
        + Var[fun ω => kde K h (fun i => X i ω) t; P] := by
  obtain ⟨C, hC⟩ := hK_bdd
  have hterm : ∀ i, MemLp (fun ω => K ((t - X i ω) / h)) 2 P := by
    intro i
    refine MemLp.of_bound ?_ C ?_
    · exact (hK_meas.comp_aemeasurable
        (((hX i).aemeasurable.const_sub t).div_const h)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact hC _
  have hY : MemLp (fun ω => kde K h (fun i => X i ω) t) 2 P := by
    have hsum := memLp_finsetSum Finset.univ (fun i _ => hterm i)
    have hmul := hsum.const_mul (((n : ℝ) * h)⁻¹)
    simpa only [kde] using hmul
  exact kde_mse_eq_of_memLp hY

/-- Under a density bounded by `B`, a positive bandwidth and `∫ K² < ∞`, the KDE has a finite
second moment with no bound on `K`: the sample law is at most `B • volume`, under which each
`x ↦ K ((t - x) / h) ^ 2` is integrable. -/
private lemma memLp_kde_of_integrable_sq {K f : ℝ → ℝ} {B : ℝ} (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_sq : Integrable fun u => K u ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    {h : ℝ} (hh : 0 < h) (t : ℝ) :
    MemLp (fun ω => kde K h (fun i => X i ω) t) 2 P := by
  have hle : (volume.withDensity fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal B • volume := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hf_le x))
  have hvol : Integrable fun x => K ((t - x) / h) ^ 2 := by
    refine ((measurePreserving_sub_right volume t).integrable_comp_of_integrable
      (hK_sq.comp_div (neg_ne_zero.mpr hh.ne'))).congr ?_
    filter_upwards with x
    simp only [Function.comp_apply, div_neg, ← neg_div, neg_sub]
  have hsq : Integrable (fun x => K ((t - x) / h) ^ 2)
      (volume.withDensity fun x => ENNReal.ofReal (f x)) :=
    (hvol.smul_measure ENNReal.ofReal_ne_top).mono_measure hle
  have hterm : ∀ i, MemLp (fun ω => K ((t - X i ω) / h)) 2 P := fun i =>
    (memLp_two_iff_integrable_sq (hK_meas.comp_aemeasurable
      (((hX i).aemeasurable.const_sub t).div_const h)).aestronglyMeasurable).mpr
      ((hX i).integrable_comp hsq)
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hterm i)
  have hmul := hsum.const_mul (((n : ℝ) * h)⁻¹)
  simpa only [kde] using hmul

/-- **Mean-squared-error consistency of the KDE.** At a continuity point `t` of a bounded,
nonnegative, measurable density `f`, for an integrable measurable kernel `K` with `∫ K = 1` and
`∫ K² < ∞`, independent samples with density `f`, and deterministic bandwidths `h_N > 0` with
`h_N → 0` and `(N + 1) h_N → ∞`, the mean squared error
`E[(f̂_{h_N}(t) - f(t))²]` of the estimator built from the first `N + 1` samples tends to `0`.
`K` need not be bounded: `∫ K² < ∞` and the bounded density give the estimator a finite second
moment, so the error is squared bias plus variance by
`meanSquaredError_eq_variance_add_sq_expectation_sub`; the bias vanishes by `integral_kde_eq`
and `kernel_smoothing_tendsto`, the variance by `variance_kde_le`. -/
theorem kde_mse_tends_to_zero {K f : ℝ → ℝ} {t B : ℝ} {hh : ℕ → ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hK_sq : Integrable fun u => K u ^ 2)
    (hcont : ContinuousAt f t)
    (hh_pos : ∀ N, 0 < hh N) (hh_lim : Tendsto hh atTop (𝓝 0))
    (hh_n : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * hh N) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    (hindep : iIndepFun X P) :
    Tendsto (fun N : ℕ => ∫ ω, (kde K (hh N) (fun i : Fin (N + 1) => X i ω) t - f t) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hh_within : Tendsto hh atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hh_lim, Eventually.of_forall hh_pos⟩
  have hexp : ∀ N, (∫ ω, kde K (hh N) (fun i : Fin (N + 1) => X i ω) t ∂P)
      = ∫ u, K u * f (t - hh N * u) := fun N =>
    integral_kde_eq (Nat.succ_pos N) hf_meas hf_nonneg hf_le
      (fun i => hX i) hK_meas hK_int (hh_pos N) t
  have hbias : Tendsto
      (fun N : ℕ => (∫ ω, kde K (hh N) (fun i : Fin (N + 1) => X i ω) t ∂P) - f t)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => ∫ u, K u * f (t - hh N * u)) atTop (𝓝 (f t)) := by
      have hcomp := (kernel_smoothing_tendsto hf_meas hf_nonneg hf_le
        hK_int hK_one hcont).comp hh_within
      simpa [Function.comp_def] using hcomp
    have hcongr : (fun N : ℕ =>
            (∫ ω, kde K (hh N) (fun i : Fin (N + 1) => X i ω) t ∂P) - f t)
        = fun N : ℕ => (∫ u, K u * f (t - hh N * u)) - f t := by
      funext N
      rw [hexp N]
    rw [hcongr]
    have hsub := hlim.sub_const (f t)
    simpa [sub_self] using hsub
  have hbias2 : Tendsto (fun N : ℕ =>
      ((∫ ω, kde K (hh N) (fun i : Fin (N + 1) => X i ω) t ∂P) - f t) ^ 2)
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    have h := hbias.pow 2
    rwa [h0] at h
  have hvar : Tendsto
      (fun N : ℕ => Var[fun ω => kde K (hh N) (fun i : Fin (N + 1) => X i ω) t; P])
      atTop (𝓝 0) := by
    have hbound : Tendsto
        (fun N : ℕ => B * (∫ u, K u ^ 2) / (((N + 1 : ℕ) : ℝ) * hh N))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hh_n
    refine squeeze_zero (fun N => variance_nonneg _ _) (fun N => ?_) hbound
    exact variance_kde_le (Nat.succ_pos N) (hindep.precomp Fin.val_injective)
      hf_meas hf_nonneg hf_le (fun i => hX i) hK_meas hK_sq (hh_pos N) t
  have hmse : Tendsto (fun N : ℕ =>
      ((∫ ω, kde K (hh N) (fun i : Fin (N + 1) => X i ω) t ∂P) - f t) ^ 2
        + Var[fun ω => kde K (hh N) (fun i : Fin (N + 1) => X i ω) t; P])
      atTop (𝓝 0) := by
    have h := hbias2.add hvar
    rwa [add_zero] at h
  refine Tendsto.congr' ?_ hmse
  filter_upwards with N
  exact (kde_mse_eq_of_memLp (memLp_kde_of_integrable_sq hf_le hK_meas hK_sq
    (fun i : Fin (N + 1) => hX i) (hh_pos N) t)).symm

end ProbabilityTheory
