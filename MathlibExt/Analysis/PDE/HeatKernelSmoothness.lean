/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelInitialValue
public import MathlibExt.Analysis.SpecialFunctions.GaussianMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Joint positive-time smoothness of heat evolution

The existing heat convolution is jointly `C∞` in time and space on `(0, ∞) × ℝ`
for bounded measurable real data. Factoring the Gaussian expresses it through
the zeroth Gaussian moment with smooth parameter maps. This gives all finite
orders at once, including the joint `C³` hypothesis used by Cole–Hopf.

Positive diffusivity follows by time scaling. Smoothness restricts to any
positive-time spatial domain; no smoothness at time zero or recovery of
pointwise initial values for discontinuous data is asserted.

Reference: M. Schmidt, *Partial Differential Equations*, HWS 2025, Chapter 4,
Theorem 4.3 and its proof,
https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf.
The source states bounded continuous data; the positive-time smoothing argument
only needs the bounded measurable hypothesis used here.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ContDiff
open MathlibExt.Analysis.GaussianMoments

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- Factor the heat convolution through the zeroth Gaussian moment. -/
theorem heatSolution_eq_gaussianMoment (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ((4 * π * t) ^ (-(1 : ℝ) / 2) * exp (-x ^ 2 / (4 * t))) *
      gaussianMoment f 0 (1 / (4 * t), x / (2 * t)) := by
  rw [heatSolution_of_pos f ht, gaussianMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [pow_zero, one_mul]
  have he : exp (-(x - y) ^ 2 / (4 * t)) =
      exp (-x ^ 2 / (4 * t)) * exp (-(1 / (4 * t)) * y ^ 2 + x / (2 * t) * y) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  rw [heatKernel_real, he]
  ring

/-- The heat evolution of bounded measurable data is jointly smooth at positive time. -/
theorem heatSolution_contDiffOn {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) :
    ContDiffOn ℝ ∞ (Function.uncurry (heatSolution f)) (Ioi 0 ×ˢ univ) := by
  have ht (p : ℝ × ℝ) (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) : p.1 ≠ 0 := ne_of_gt hp.1
  have h₄ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 4 * p.1) (Ioi 0 ×ˢ univ) := by fun_prop
  have h₂ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * p.1) (Ioi 0 ×ˢ univ) := by fun_prop
  have ha : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 1 / (4 * p.1)) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div h₄ (fun p hp => mul_ne_zero (by norm_num) (ht p hp))
  have hb' : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 / (2 * p.1)) (Ioi 0 ×ˢ univ) :=
    contDiff_snd.contDiffOn.div h₂ (fun p hp => mul_ne_zero (by norm_num) (ht p hp))
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      gaussianMoment f 0 (1 / (4 * p.1), p.2 / (2 * p.1))) (Ioi 0 ×ˢ univ) :=
    (gaussianMoment_contDiffOn hf hb 0).comp (ha.prodMk hb') (fun p hp =>
      ⟨one_div_pos.mpr (mul_pos (by norm_num) hp.1), mem_univ _⟩)
  have hn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (4 * π * p.1) ^ (-(1 : ℝ) / 2))
      (Ioi 0 ×ˢ univ) := by
    apply ContDiffOn.rpow_const_of_ne (by fun_prop)
    intro p hp
    exact mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (ht p hp)
  have he : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => exp (-p.2 ^ 2 / (4 * p.1)))
      (Ioi 0 ×ˢ univ) :=
    ((contDiff_snd.contDiffOn.pow 2).neg.div h₄
      (fun p hp => mul_ne_zero (by norm_num) (ht p hp))).exp
  exact ((hn.mul he).mul hm).congr (fun p hp => heatSolution_eq_gaussianMoment f hp.1 p.2)

/-- The joint smoothness theorem applies at every positive-time point. -/
theorem heatSolution_contDiffAt {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (Function.uncurry (heatSolution f)) p :=
  (heatSolution_contDiffOn hf hb).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)

/-- Positive diffusivity preserves joint positive-time smoothness. -/
theorem heatSolution_contDiffOn_scaled {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn hf hb).comp
    ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ hp => ⟨mul_pos hν hp.1, mem_univ _⟩)

/-- Restrict the smooth heat evolution to a positive-time rectangle. Neither the
time set nor the spatial set needs to be bounded. -/
theorem heatSolution_contDiffOn_rectangle {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {I J : Set ℝ} (hI : I ⊆ Ioi 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (heatSolution f)) (I ×ˢ J) :=
  (heatSolution_contDiffOn hf hb).mono (fun _ hp => ⟨hI hp.1, mem_univ _⟩)

end MathlibExt.Analysis.PDE.HeatKernel
