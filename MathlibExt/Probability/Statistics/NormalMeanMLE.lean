/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Probability.Statistics.Likelihood
public import MathlibExt.Probability.Statistics.SampleMeanSquaredDeviation

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Maximum likelihood for a normal mean with known variance

For the real Gaussian density family with fixed positive variance, the iid likelihood of a
nonempty sample has its unique maximum at the sample mean. This follows from the strict
least-squares characterization of the sample mean, without assuming distinct observations.
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.FiniteProbability
open scoped BigOperators ENNReal NNReal Real

namespace ProbabilityTheory

/-- **Normal location family with fixed variance.** For a positive variance $v$ and parameter
$m\in\mathbb R$, the normal location family has density $\mathcal N(m,v)$ with respect to
Lebesgue measure; only its mean $m$ varies. -/
noncomputable def gaussianMeanFamily (v : ℝ≥0) (hv : v ≠ 0) :
    NormalizedDensityFamily ℝ ℝ volume where
  dens m := gaussianPDF m v
  measurable m := (measurable_gaussianPDF m v).aemeasurable
  normalized m := lintegral_gaussianPDF_eq_one m hv

private theorem gaussianMeanLikelihood_ne_top {v : ℝ≥0} (hv : v ≠ 0)
    {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    (gaussianMeanFamily v hv).iidLikelihood n m x ≠ ∞ :=
  ENNReal.prod_ne_top fun _ _ => gaussianPDF_ne_top

private theorem gaussianMeanLikelihood_toReal_pos {v : ℝ≥0} (hv : v ≠ 0)
    {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    0 < ((gaussianMeanFamily v hv).iidLikelihood n m x).toReal := by
  simp only [NormalizedDensityFamily.iidLikelihood, gaussianMeanFamily, ENNReal.toReal_prod,
    toReal_gaussianPDF]
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos m v (x i) hv

private theorem log_gaussianMeanLikelihood {v : ℝ≥0} (hv : v ≠ 0)
    {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    Real.log ((gaussianMeanFamily v hv).iidLikelihood n m x).toReal =
      n * Real.log ((√(2 * π * v : ℝ))⁻¹) - (∑ i, (x i - m) ^ 2) / (2 * v) := by
  simp only [NormalizedDensityFamily.iidLikelihood, gaussianMeanFamily, ENNReal.toReal_prod,
    toReal_gaussianPDF]
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos m v (x i) hv).ne')]
  have hvNN : 0 < v := pos_iff_ne_zero.mpr hv
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hvNN
  have h (i : Fin n) : Real.log (gaussianPDFReal m v (x i)) =
      Real.log ((√(2 * π * v : ℝ))⁻¹) - (x i - m) ^ 2 / (2 * v) := by
    rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_div]

/-- **The sample mean maximizes the normal likelihood with known variance.** Let $n>0$ and
$x_1,\ldots,x_n\in\mathbb R$. For the iid normal location family with fixed variance $v>0$,
$m$ maximizes the product of the normal densities at the observations if and only if
$m=\bar x$, the sample mean. -/
theorem isMaxOn_gaussianMeanLikelihood_iff {v : ℝ≥0} (hv : v ≠ 0) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (m : ℝ) :
    IsMaxOn (fun a => (gaussianMeanFamily v hv).iidLikelihood n a x) Set.univ m ↔
      m = sampleMean x := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hvNN : 0 < v := pos_iff_ne_zero.mpr hv
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hvNN
  have hstrict (a : ℝ) (ha : a ≠ sampleMean x) :
      (gaussianMeanFamily v hv).iidLikelihood n a x <
        (gaussianMeanFamily v hv).iidLikelihood n (sampleMean x) x := by
    refine (ENNReal.toReal_lt_toReal (gaussianMeanLikelihood_ne_top hv x a)
      (gaussianMeanLikelihood_ne_top hv x (sampleMean x))).mp (lt_of_not_ge ?_)
    intro hle
    have hlogs := Real.log_le_log (gaussianMeanLikelihood_toReal_pos hv x _) hle
    rw [log_gaussianMeanLikelihood hv x, log_gaussianMeanLikelihood hv x] at hlogs
    have hs := sum_sq_sub_sampleMean_lt x ha
    exact (not_le_of_gt (sub_lt_sub_left (div_lt_div_of_pos_right hs (by positivity)) _)) hlogs
  rw [isMaxOn_univ_iff]
  constructor
  · intro h
    by_contra hne
    exact (not_le_of_gt (hstrict m hne)) (h (sampleMean x))
  · rintro rfl a
    by_cases ha : a = sampleMean x
    · simp [ha]
    · exact (hstrict a ha).le

end ProbabilityTheory
