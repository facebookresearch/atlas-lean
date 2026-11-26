/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standard-normal upper-tail bound

This module proves an upper-tail bound for the standard normal law: for `0 ≤ u`, the mass of
`(u, ∞)` under `gaussianReal 0 1` is at most `Real.exp (-u ^ 2 / 2) / 2`.

## Main results

* `ProbabilityTheory.gaussianReal_Ioi_zero`: a centered Gaussian law with positive variance gives
  mass `1 / 2` to `(0, ∞)`.
* `ProbabilityTheory.gaussianReal_Ioi_le_half_exp`: the standard-normal upper-tail bound.

The proof compares densities after shifting the mean by `u`: on `(u, ∞)` the standard density is
pointwise at most `Real.exp (-u ^ 2 / 2)` times the density of `gaussianReal u 1`, so the tail is
at most `Real.exp (-u ^ 2 / 2)` times the mass of `(u, ∞)` under `gaussianReal u 1`. By
translation that mass is the half-line mass of `gaussianReal 0 1` at zero, which is `1 / 2` by
symmetry.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace ProbabilityTheory

private lemma pdf_le {u x : ℝ} (hu : 0 ≤ u) (hx : u ≤ x) :
    gaussianPDFReal 0 1 x ≤ Real.exp (-u ^ 2 / 2) * gaussianPDFReal u 1 x := by
  have hsq : u ^ 2 + (x - u) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hx)]
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hC : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hexp : Real.exp (-x ^ 2 / 2)
      ≤ Real.exp (-u ^ 2 / 2) * Real.exp (-(x - u) ^ 2 / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hsq]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹
          * (Real.exp (-u ^ 2 / 2) * Real.exp (-(x - u) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = Real.exp (-u ^ 2 / 2)
          * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x - u) ^ 2 / 2)) := by
        ring

private lemma integral_le {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 1 (Set.Ioi u)
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal u 1 (Set.Ioi u) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by simp
  rw [gaussianReal_apply 0 h1, gaussianReal_apply u h1,
    ← lintegral_const_mul _ (measurable_gaussianPDF u 1)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  rw [Set.mem_Ioi] at hx
  have hle := pdf_le hu (le_of_lt hx)
  simp only [gaussianPDF] at hle ⊢
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

private lemma translate_eq {u : ℝ} :
    gaussianReal u 1 (Set.Ioi u) = gaussianReal 0 1 (Set.Ioi 0) := by
  have hmap := gaussianReal_map_const_add (μ := u) (v := 1) (-u)
  rw [add_neg_cancel] at hmap
  have hpre : (fun x : ℝ => -u + x) ⁻¹' Set.Ioi 0 = Set.Ioi u := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  calc gaussianReal u 1 (Set.Ioi u)
      = gaussianReal u 1 ((fun x : ℝ => -u + x) ⁻¹' Set.Ioi 0) := by rw [hpre]
    _ = Measure.map (fun x : ℝ => -u + x) (gaussianReal u 1) (Set.Ioi 0) :=
        (Measure.map_apply (measurable_const_add _) measurableSet_Ioi).symm
    _ = gaussianReal 0 1 (Set.Ioi 0) := by rw [hmap]

/-- **Half-line mass of a centered Gaussian.** A centered Gaussian law with variance `v ≠ 0`
gives mass `1/2` to `(0, ∞)`, by symmetry and because it has no atoms; this is the value
`P(B_t > 0) = 1/2` used in Le Gall's proof of the oscillation of Brownian motion at time `0` (ENS
notes *Intégration, Probabilités et Processus Aléatoires*, proof of Corollaire 14.4.3). -/
lemma gaussianReal_Ioi_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Set.Ioi 0) = 1 / 2 := by
  have hsymm : gaussianReal 0 v (Set.Iio 0) = gaussianReal 0 v (Set.Ioi 0) := by
    have h := gaussianReal_map_neg (μ := 0) (v := v)
    rw [neg_zero] at h
    conv_lhs => rw [← h]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp
  have : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  have htot : gaussianReal 0 v (Set.Iio 0) + gaussianReal 0 v (Set.Ioi 0) = 1 := by
    rw [measure_congr (Iio_ae_eq_Iic (a := (0 : ℝ))), ← Set.compl_Ioi,
      prob_compl_eq_one_sub measurableSet_Ioi]
    exact tsub_add_cancel_of_le prob_le_one
  rw [hsymm] at htot
  have hfin : gaussianReal 0 v (Set.Ioi 0) ≠ ∞ := measure_ne_top _ _
  rw [← two_mul] at htot
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), htot]

private lemma half_eq : gaussianReal 0 1 (Set.Ioi 0) = ENNReal.ofReal (1 / 2 : ℝ) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by simp
  have h := gaussianReal_Ioi_zero h1
  rw [h, ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
  simp

/-- **Standard-normal upper-tail bound.** For `0 ≤ u`, the mass of `(u, ∞)` under the
standard normal law `gaussianReal 0 1` is at most `Real.exp (-u ^ 2 / 2) / 2`. On `(u, ∞)` the
standard density is at most `Real.exp (-u ^ 2 / 2)` times the density of `gaussianReal u 1`, which
gives `(u, ∞)` mass `1 / 2`. -/
theorem gaussianReal_Ioi_le_half_exp {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 1 (Set.Ioi u) ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2) / 2) := by
  have hE : (0 : ℝ) ≤ Real.exp (-u ^ 2 / 2) := Real.exp_nonneg _
  calc gaussianReal 0 1 (Set.Ioi u)
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal u 1 (Set.Ioi u) :=
        integral_le hu
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * gaussianReal 0 1 (Set.Ioi 0) := by
        rw [translate_eq]
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) * ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [half_eq]
    _ = ENNReal.ofReal (Real.exp (-u ^ 2 / 2) / 2) := by
        rw [← ENNReal.ofReal_mul hE]
        congr 1
        ring

end ProbabilityTheory
