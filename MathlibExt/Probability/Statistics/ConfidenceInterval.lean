/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HoeffdingBernoulliSumAbsTail
public import MathlibExt.Probability.MonteCarloRate

/-!
# Finite-sample confidence intervals

Non-asymptotic frequentist coverage for a Bernoulli mean (Hoeffding) and an IID
square-integrable mean with a known deterministic variance bound (Chebyshev).
The Hoeffding interval is closed; the Chebyshev interval is open, matching the
strict and non-strict tail bounds respectively. These are not normal, Student-t,
or sample-variance plug-in intervals.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A Bernoulli sample mean lies within the explicit Hoeffding radius of its
fixed population mean with probability at least `1 - α`. The confidence level
is nonvacuous (`0 < α < 1`), and the finite sample is nonempty. -/
theorem bernoulli_mean_hoeffding_ci {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (p α : ℝ) (hIndep : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hBernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hexp : ∀ i, ∫ x, X i x ∂μ = p) (hα : 0 < α) (hα1 : α < 1) :
    1 - α ≤ μ.real {ω | |(∑ i, X i ω) / n - p| ≤
      Real.sqrt (Real.log (2 / α) / (2 * n))} := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (2 / α) := Real.log_pos ((lt_div_iff₀ hα).2 (by linarith))
  have hrad : 0 < Real.log (2 / α) / (2 * n) := div_pos hlog (by positivity)
  let r := Real.sqrt (Real.log (2 / α) / (2 * n))
  have hr : 0 < r := Real.sqrt_pos.2 hrad
  have htail := hoeffding_bernoulli_sum_abs_tail X p r hIndep hmeas hBernoulli hexp hr
  have hbound : 2 * Real.exp (-2 * r ^ 2 * (n : ℝ)) = α := by
    dsimp [r]
    rw [Real.sq_sqrt hrad.le]
    have he : -2 * (Real.log (2 / α) / (2 * (n : ℝ))) * n = -Real.log (2 / α) := by
      field_simp
    rw [he, Real.exp_neg, Real.exp_log (div_pos (by norm_num) hα)]
    field_simp
  rw [hbound] at htail
  have hsum : AEMeasurable (fun ω => ∑ i, X i ω) μ :=
    Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hmeas i)
  have hcov : NullMeasurableSet {ω | |(∑ i, X i ω) / n - p| ≤ r} μ := by
    simpa only [Real.norm_eq_abs] using
      nullMeasurableSet_le ((hsum.div_const n).sub_const p).norm (aemeasurable_const (b := r))
  have hevent : {ω | |(∑ i, X i ω) / n - p| ≤ r}ᶜ =
      {ω | r * n < |(∑ i, X i ω) - n * p|} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    have he : (∑ i, X i ω) / n - p = ((∑ i, X i ω) - n * p) / n := by
      field_simp
    rw [he, abs_div, abs_of_pos hnR, lt_div_iff₀ hnR]
  have hc := probReal_compl_eq_one_sub₀ hcov
  rw [hevent] at hc
  change 1 - α ≤ μ.real {ω | |(∑ i, X i ω) / n - p| ≤ r}
  linarith

private lemma integral_sample_mean_of_identDistrib (X : ℕ → Ω → ℝ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hMemLp : MemLp (X 0) 2 μ)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ ω, (∑ i ∈ Finset.range n, X i ω) / (n : ℝ) ∂μ) = ∫ ω, X 0 ω ∂μ := by
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    ((hIdent i).memLp_iff.mpr hMemLp).integrable (by norm_num))]
  simp_rw [(hIdent _).integral_eq]
  simp [Nat.cast_ne_zero.mpr hn]

/-- An IID square-integrable sample mean lies in the open Chebyshev error band
with probability at least `1 - α`. Here `v` is a positive, known, deterministic
upper bound on the population variance, not an estimated sample variance.
For `α ≥ 1` the valid inequality has a nonpositive, hence vacuous, lower bound. -/
theorem sample_mean_chebyshev_ci (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hMemLp : MemLp (X 0) 2 μ)
    {n : ℕ} (hn : n ≠ 0) {v α : ℝ} (hv : 0 < v)
    (hvar : variance (X 0) μ ≤ v) (hα : 0 < α) :
    1 - α ≤ μ.real {ω | |(∑ i ∈ Finset.range n, X i ω) / n - ∫ x, X 0 x ∂μ| <
      Real.sqrt (v / (n * α))} := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let Y : Ω → ℝ := fun ω => (∑ i ∈ Finset.range n, X i ω) / n
  have hY : MemLp Y 2 μ := by
    simpa only [Y, div_eq_inv_mul] using
      (memLp_finsetSum (Finset.range n) (fun i _ => (hIdent i).memLp_iff.mpr hMemLp)).const_mul
        (n : ℝ)⁻¹
  have hmean : (∫ ω, Y ω ∂μ) = ∫ ω, X 0 ω ∂μ :=
    integral_sample_mean_of_identDistrib X hIdent hMemLp hn
  have hrad : 0 < v / (n * α) := div_pos hv (mul_pos hnR hα)
  let r := Real.sqrt (v / (n * α))
  have hr : 0 < r := Real.sqrt_pos.2 hrad
  have htail := meas_ge_le_variance_div_sq hY hr
  have hratio : variance Y μ / r ^ 2 ≤ α := by
    rw [MathlibExt.Probability.variance_sample_mean_of_iid X hIndep hIdent hMemLp n hn]
    dsimp [r]
    rw [Real.sq_sqrt hrad.le]
    calc variance (X 0) μ / n / (v / (n * α)) ≤ v / n / (v / (n * α)) := by
          gcongr
        _ = α := by field_simp
  have htailR : μ.real {ω | r ≤ |Y ω - ∫ x, X 0 x ∂μ|} ≤ α := by
    rw [← hmean]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (htail.trans (ENNReal.ofReal_le_ofReal hratio))).trans_eq (ENNReal.toReal_ofReal hα.le)
  have hcov : NullMeasurableSet {ω | |Y ω - ∫ x, X 0 x ∂μ| < r} μ := by
    simpa only [Real.norm_eq_abs] using nullMeasurableSet_lt
      (hY.aemeasurable.sub_const (∫ x, X 0 x ∂μ)).norm (aemeasurable_const (b := r))
  have hc := probReal_compl_eq_one_sub₀ hcov
  simp only [Set.compl_ofPred, not_lt] at hc
  change 1 - α ≤ μ.real {ω | |Y ω - ∫ x, X 0 x ∂μ| < r}
  linarith

end ProbabilityTheory
