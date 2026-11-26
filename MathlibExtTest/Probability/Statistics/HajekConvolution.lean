/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.HajekConvolution
import MathlibExt.Probability.Statistics.Contiguity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Statistics.HajekConvolution

-- The first experiment has singular alternatives. Thereafter the observation is N(h, 1),
-- and adding a fixed bias c gives a regular estimator with limit law N(c, 1).
example (c : ℝ) : ∃ M : ProbabilityMeasure ℝ,
    gaussianReal c 1 = gaussianReal 0 1 ∗ (M : Measure ℝ) := by
  let P (n : ℕ) (h : ℝ) : ProbabilityMeasure ℝ :=
    if n = 0 then ⟨Measure.dirac h, inferInstance⟩ else ⟨gaussianReal h 1, inferInstance⟩
  have hLAN (h : ℝ) : llr (gaussianReal h 1) (gaussianReal 0 1) =ᵐ[gaussianReal 0 1]
      fun x => h * x - h ^ 2 / 2 := by
    let w := fun x : ℝ => ENNReal.ofReal (Real.exp (h * x - h ^ 2 / 2))
    have he : (gaussianReal 0 1).withDensity w = gaussianReal h 1 := by
      simpa [w] using MathlibExt.Probability.Statistics.Contiguity.gaussianReal_withDensity_exp h 1
    rw [← he, llr_def]
    filter_upwards [Measure.rnDeriv_withDensity (gaussianReal 0 1)
      (show Measurable w by dsimp [w]; fun_prop)] with x hx
    simp [hx, w, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hΔ : Tendsto (fun n => (P n 0).map id) atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact Subtype.ext (by simp [P, hn, ProbabilityMeasure.map])
  have herr (h ε : ℝ) (hε : 0 < ε) : Tendsto (fun n => (P n 0 : Measure ℝ)
      {x | ε ≤ |llr (P n h : Measure ℝ) (P n 0) x - (h * x - h ^ 2 / 2)|}) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [P, hn]
    symm
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hLAN h] with x hx
    simpa [hx] using hε.not_ge
  have hreg (h : ℝ) : Tendsto (fun n => (P n h).map (fun x => x + c - h)) atTop
      (𝓝 ⟨gaussianReal c 1, inferInstance⟩) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    apply Subtype.ext
    simp only [P, hn]
    change gaussianReal c 1 = (gaussianReal h 1).map (fun x => x + c - h)
    have he (x : ℝ) : x + c - h = x - (h - c) := by ring
    simp only [he, gaussianReal_map_sub_const, sub_sub_cancel]
  simpa using MathlibExt.Probability.Statistics.EfficiencyWanted.hajek_convolution
    (Ω := fun _ => ℝ) P (fun _ => id) (fun _ => measurable_id) (I := 1) zero_lt_one
    hΔ (by simpa using herr) (fun _ x => x + c) (fun _ => measurable_id.add_const c)
    ⟨gaussianReal c 1, inferInstance⟩ hreg

end MathlibExtTest.Probability.Statistics.HajekConvolution
