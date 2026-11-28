/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ANOVA.OneWay
public import MathlibExt.Probability.Statistics.EstimationRisk
public import MathlibExt.Probability.Distributions.GammaMoments

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Mean squared error of two Gaussian variance estimators

`ProbabilityTheory.gaussian_variance_estimators_mse` compares the estimators for an i.i.d.
`N(μ, v)` sample of size `n ≥ 2` with `v > 0`. The one-group ANOVA chi-square law gives
the distribution of the scaled sum of squared deviations. Gamma moments and the bias–variance
decomposition then give the exact risks and their strict ordering.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

open MathlibExt.Probability.Statistics.EstimationRisk

private theorem sample_rss_law {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    HasLaw (fun x : Fin n → ℝ =>
      (∑ i, (x i - (∑ j, x j) / (n : ℝ)) ^ 2) / (v : ℝ))
      (chiSquareMeasure (n - 1)) (Measure.pi fun _ : Fin n => gaussianReal μ v) := by
  have hgm (x : Fin n → ℝ) : groupMean (fun _ : Fin n => ()) x () = (∑ i, x i) / n := by
    simp [groupMean]
  have h := hasLaw_sumSqWithin_div (fun _ : Fin n => ()) (fun _ => ⟨⟨0, by omega⟩, rfl⟩)
    (by simp only [Fintype.card_unit, Fintype.card_fin]; omega) (m0 := μ) hv
    (HasLaw.id (μ := Measure.pi fun _ : Fin n => gaussianReal μ v))
  simpa [sumSqWithin, hgm, id] using h

@[expose] public section

/-- **A biased variance estimator with smaller mean squared error.** For an i.i.d. sample
of size `n ≥ 2` from a normal law with mean `μ` and variance `v > 0`, let `Q` be the sum
of squared deviations from the sample mean. The estimators `S = Q / (n - 1)` and `W = Q / n`
are square-integrable. The former is unbiased and has mean squared error `2 * v^2 / (n - 1)`.
The latter has bias `-v / n` and mean squared error `(2 * n - 1) * v^2 / n^2`, which is strictly
smaller than the former's. -/
theorem gaussian_variance_estimators_mse {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    let P := Measure.pi fun _ : Fin n => gaussianReal μ v
    let Q := fun x : Fin n → ℝ => ∑ i, (x i - (∑ j, x j) / (n : ℝ)) ^ 2
    let S := fun x => Q x / ((n : ℝ) - 1)
    let W := fun x => Q x / (n : ℝ)
    MemLp S 2 P ∧ MemLp W 2 P ∧
      (∫ x, S x ∂P) = (v : ℝ) ∧ (∫ x, W x ∂P) - (v : ℝ) = -(v : ℝ) / n ∧
      (∫ x, (S x - v) ^ 2 ∂P) = 2 * (v : ℝ) ^ 2 / ((n : ℝ) - 1) ∧
      (∫ x, (W x - v) ^ 2 ∂P) = (2 * (n : ℝ) - 1) * (v : ℝ) ^ 2 / (n : ℝ) ^ 2 ∧
      (∫ x, (W x - v) ^ 2 ∂P) < ∫ x, (S x - v) ^ 2 ∂P := by
  intro P Q S W
  let law : ProbabilityMeasure (Fin n → ℝ) := ⟨P, inferInstance⟩
  let Z := fun x => Q x / (v : ℝ)
  have hZ : HasLaw Z (chiSquareMeasure (n - 1)) P := sample_rss_law hn μ hv
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hk : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
    linarith
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hZp : MemLp Z 2 P := hZ.memLp (memLp_id_gammaMeasure hk hr)
  have hZmean : (∫ x, Z x ∂P) = (n : ℝ) - 1 := by
    rw [hZ.integral_eq, chiSquareMeasure, integral_id_gammaMeasure hk hr,
      Nat.cast_sub hn1, Nat.cast_one]
    ring
  have hZvar : variance Z P = 2 * ((n : ℝ) - 1) := by
    rw [hZ.variance_eq, chiSquareMeasure, variance_id_gammaMeasure hk hr,
      Nat.cast_sub hn1, Nat.cast_one]
    ring
  have hscale (d : ℝ) : (fun x => Q x / d) = fun x => ((v : ℝ) / d) * Z x := by
    funext x
    dsimp only [Z]
    field_simp [hvpos.ne']
  have hSp : MemLp S 2 P := by
    change MemLp (fun x => Q x / ((n : ℝ) - 1)) 2 P
    rw [hscale]
    exact hZp.const_mul _
  have hWp : MemLp W 2 P := by
    change MemLp (fun x => Q x / (n : ℝ)) 2 P
    rw [hscale]
    exact hZp.const_mul _
  have hSmean : (∫ x, S x ∂P) = (v : ℝ) := by
    change (∫ x, Q x / ((n : ℝ) - 1) ∂P) = _
    rw [hscale, integral_const_mul, hZmean]
    exact div_mul_cancel₀ _ (sub_pos.mpr hnR).ne'
  have hWbias : (∫ x, W x ∂P) - (v : ℝ) = -(v : ℝ) / (n : ℝ) := by
    change (∫ x, Q x / (n : ℝ) ∂P) - (v : ℝ) = _
    rw [hscale, integral_const_mul, hZmean]
    field_simp
    ring
  have hSmse : (∫ x, (S x - v) ^ 2 ∂P) = 2 * (v : ℝ) ^ 2 / ((n : ℝ) - 1) := by
    have h := meanSquaredError_eq_variance_add_sq_expectation_sub
      (μ := law) (θ := (v : ℝ)) hSp
    change (∫ x, (S x - v) ^ 2 ∂P) = variance S P + ((∫ x, S x ∂P) - v) ^ 2 at h
    rw [h, hSmean, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    change variance (fun x => Q x / ((n : ℝ) - 1)) P = _
    rw [hscale, variance_const_mul, hZvar]
    field_simp [(sub_pos.mpr hnR).ne']
  have hWmse : (∫ x, (W x - v) ^ 2 ∂P) = (2 * (n : ℝ) - 1) * (v : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    have h := meanSquaredError_eq_variance_add_sq_expectation_sub
      (μ := law) (θ := (v : ℝ)) hWp
    change (∫ x, (W x - v) ^ 2 ∂P) = variance W P + ((∫ x, W x ∂P) - v) ^ 2 at h
    rw [h, hWbias]
    change variance (fun x => Q x / (n : ℝ)) P + (-(v : ℝ) / (n : ℝ)) ^ 2 = _
    rw [hscale, variance_const_mul, hZvar]
    ring
  refine ⟨hSp, hWp, hSmean, hWbias, hSmse, hWmse, ?_⟩
  rw [hWmse, hSmse, div_lt_div_iff₀ (sq_pos_of_pos hnpos) (sub_pos.mpr hnR)]
  have hdiff : 0 < 3 * (n : ℝ) - 1 := by linarith
  nlinarith [mul_pos hdiff (sq_pos_of_pos hvpos)]

end

end ProbabilityTheory
