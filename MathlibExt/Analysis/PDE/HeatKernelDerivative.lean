/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelInitialValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FunProp

/-!
# Spatial differentiation and the initial trace of heat evolution

For bounded `C¹` data with bounded derivative, spatial differentiation commutes
with heat evolution. Differentiate the rescaled convolution against its fixed
integrable Gaussian, then apply the initial-trace theorem to the derivative.
No uniform continuity or uniform-in-space convergence is assumed or asserted.

The formula also holds for the chosen nonpositive-time extension, which is the
datum itself. Positive diffusivity is handled by time scaling.

Reference: the approximate-identity construction in M. Schmidt, *Partial
Differential Equations*, HWS 2025, Chapter 4, Theorem 4.3,
https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf.
The derivative trace follows by commuting the derivative and applying that
initial-value argument to the bounded continuous derivative.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem hasDerivAt_rescaled {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M) (t x : ℝ) :
    HasDerivAt (fun z => ∫ y, heatKernel ℝ 1 y * f (z - sqrt t * y))
      (∫ y, heatKernel ℝ 1 y * deriv f (x - sqrt t * y)) x := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨D, hD⟩ := hdb
  have hfc (z : ℝ) : Continuous (fun y => f (z - sqrt t * y)) :=
    hf.continuous.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hdc (z : ℝ) : Continuous (fun y => deriv f (z - sqrt t * y)) :=
    hf.continuous_deriv_one.comp (continuous_const.sub (continuous_const.mul continuous_id))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => heatKernel ℝ 1 y * f (z - sqrt t * y))
    (F' := fun z y => heatKernel ℝ 1 y * deriv f (z - sqrt t * y))
    (s := univ) (bound := fun y => heatKernel ℝ 1 y * D) univ_mem ?_ ?_ ?_ ?_
    ((integrable_heatKernel (E := ℝ) one_pos).mul_const D) ?_).2
  · exact Eventually.of_forall (fun z =>
      ((heatKernel_contDiff 1).continuous.mul (hfc z)).aestronglyMeasurable)
  · exact (integrable_heatKernel (E := ℝ) one_pos).mul_bdd (hfc x).aestronglyMeasurable
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hM (x - sqrt t * y)))
  · exact ((heatKernel_contDiff 1).continuous.mul (hdc x)).aestronglyMeasurable
  · filter_upwards with y z _
    rw [norm_mul, Real.norm_eq_abs (heatKernel ℝ 1 y), abs_of_pos (heatKernel_pos one_pos y)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using hD (z - sqrt t * y)) (heatKernel_pos one_pos y).le
  · filter_upwards with y z _
    simpa using! (((hf.differentiable (by norm_num)) (z - sqrt t * y)).hasDerivAt.comp z
      ((hasDerivAt_id' z).sub_const (sqrt t * y))).const_mul (heatKernel ℝ 1 y)

/-- Spatial differentiation commutes with heat evolution for bounded `C¹` data
with bounded derivative. The statement includes the chosen nonpositive-time extension. -/
theorem heatSolution_hasDerivAt_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M) (t x : ℝ) :
    HasDerivAt (heatSolution f t) (heatSolution (deriv f) t x) x := by
  by_cases ht : 0 < t
  · have he : heatSolution f t = fun z => ∫ y, heatKernel ℝ 1 y * f (z - sqrt t * y) :=
      funext (heatSolution_rescaled f ht)
    rw [he, heatSolution_rescaled (deriv f) ht]
    exact hasDerivAt_rescaled hf hb hdb t x
  · have he : heatSolution f t = f := funext (heatSolution_of_nonpos f (le_of_not_gt ht))
    rw [he, heatSolution_of_nonpos _ (le_of_not_gt ht)]
    exact (hf.differentiable (by norm_num) x).hasDerivAt

/-- The derivative is the heat evolution of the initial derivative. -/
theorem deriv_heatSolution {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M) (t x : ℝ) :
    deriv (heatSolution f t) x = heatSolution (deriv f) t x :=
  (heatSolution_hasDerivAt_deriv hf hb hdb t x).deriv

/-- Spatial derivatives recover the initial derivative pointwise as time decreases to zero. -/
theorem heatSolution_deriv_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M) (x : ℝ) :
    Tendsto (fun t => deriv (heatSolution f t) x) (𝓝[>] 0) (𝓝 (deriv f x)) := by
  simp_rw [deriv_heatSolution hf hb hdb]
  exact heatSolution_tendsto_zero hf.continuous_deriv_one hdb x

/-- Positive diffusivity preserves the spatial-derivative initial trace. -/
theorem heatSolution_deriv_tendsto_zero_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    Tendsto (fun t => deriv (heatSolution f (ν * t)) x) (𝓝[>] 0) (𝓝 (deriv f x)) := by
  simp_rw [deriv_heatSolution hf hb hdb]
  exact heatSolution_tendsto_zero_scaled hf.continuous_deriv_one hdb hν x

/-- A uniform bound on the initial derivative is preserved by heat evolution. -/
theorem abs_deriv_heatSolution_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {D : ℝ} (hdb : ∀ x, |deriv f x| ≤ D) (t x : ℝ) :
    |deriv (heatSolution f t) x| ≤ D := by
  rw [deriv_heatSolution hf hb ⟨D, hdb⟩]
  exact abs_heatSolution_le hf.continuous_deriv_one hdb t x

end MathlibExt.Analysis.PDE.HeatKernel
