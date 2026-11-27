/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatWholeLine
public import MathlibExt.Analysis.PDE.HeatKernelContinuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Uniqueness of the whole-line heat-kernel construction

The existing heat convolution of continuous exponential-growth initial data has
exponential growth uniformly on every finite time strip. Consequently it is the
unique classical solution in that growth class with the same initial values.
The viscosity is positive. The initial data need only be continuous, and no
initial spatial derivative is required. All claims concern nonnegative times.

This connects the whole-line comparison theorem to the actual Gaussian solution,
with its growth, boundary continuity and PDE proved by the earlier heat modules.
Reference: Stanford Math 220B, *Heat Equation*, Theorem 20,
https://web.stanford.edu/class/math220b/handouts/heateqn.pdf, specialized to the
linear-exponential growth class formalized in `HeatWholeLine`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatWholeLine

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- The Gaussian solution has spatial exponential growth uniformly on any finite strip. -/
theorem heatSolution_hasExpGrowthOnStrip {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) {ν : ℝ} (hν : 0 ≤ ν) (T : ℝ) :
    HasExpGrowthOnStrip (fun t x => heatSolution f (ν * t) x) T := by
  obtain ⟨M, c, hM, hc, hfg⟩ := hg
  let S := sqrt |ν * T|
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * S * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  refine ⟨M * J, c, mul_nonneg hM hJ, hc, fun t ht x => ?_⟩
  have hs : |sqrt (ν * t)| ≤ S := by
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact sqrt_le_sqrt ((mul_le_mul_of_nonneg_left ht.2 hν).trans (le_abs_self _))
  have hb (y : ℝ) : |f (x - sqrt (ν * t) * y)| ≤
      (M * exp (c * |x|)) * exp (c * S * |y|) := by
    have hm : |sqrt (ν * t) * y| ≤ S * |y| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    have ha : |x - sqrt (ν * t) * y| ≤ |x| + S * |y| :=
      (abs_sub x (sqrt (ν * t) * y)).trans (add_le_add le_rfl hm)
    calc
      _ ≤ M * exp (c * |x - sqrt (ν * t) * y|) := hfg _
      _ ≤ M * exp (c * (|x| + S * |y|)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hc)) hM
      _ = _ := by simp only [mul_add, exp_add, mul_assoc]
  change |heatSolution f (ν * t) x| ≤ _
  rw [heatSolution_rescaled_all]
  have hi := integrable_heatKernel_mul_affine hf ⟨M, c, hM, hc, hfg⟩ x (sqrt (ν * t))
  calc
    _ ≤ ∫ y, |heatKernel ℝ 1 y * f (x - sqrt (ν * t) * y)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, (M * exp (c * |x|)) * (heatKernel ℝ 1 y * exp (c * S * |y|)) := by
      apply integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm)
        ((integrable_heatKernel_exp_abs one_pos (c * S)).const_mul _)
      intro y
      change |heatKernel ℝ 1 y * f (x - sqrt (ν * t) * y)| ≤
        (M * exp (c * |x|)) * (heatKernel ℝ 1 y * exp (c * S * |y|))
      rw [abs_mul, abs_of_pos (heatKernel_pos one_pos y)]
      calc
        _ ≤ heatKernel ℝ 1 y * ((M * exp (c * |x|)) * exp (c * S * |y|)) :=
          mul_le_mul_of_nonneg_left (hb y) (heatKernel_pos one_pos y).le
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; dsimp [J]; ring

/-- Every classical heat solution with the same initial data and uniform exponential
strip growth equals the actual Gaussian convolution, including both time endpoints. -/
theorem eq_heatSolution_of_exp_growth {u ut : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hf : Continuous f) (hfg : HasExpGrowth f)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (heq : ∀ t ∈ Ioc 0 T, ∀ x, ut t x = ν * iteratedDeriv 2 (u t) x)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x = f x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = heatSolution f (ν * t) x := by
  have hkc : Continuous (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) :=
    (heatSolution_continuous_of_exp_growth hf hfg).comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hkx (t : ℝ) (ht : t ∈ Ioc 0 T) (x : ℝ) :
      ContDiffAt ℝ 2 (heatSolution f (ν * t)) x := by
    have hj : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (t, x) :=
      (heatSolution_contDiffOn_scaled_of_exp_growth hf.aestronglyMeasurable hfg hν).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht.1, mem_univ x⟩)
    exact (hj.of_le (by simp)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  apply eq_of_heat_equation (v := fun t x => heatSolution f (ν * t) x)
    (vt := fun t x => ν * iteratedDeriv 2 (heatSolution f (ν * t)) x)
    (f := fun _ _ => 0) hν.le hc hkc.continuousOn hx hkx ht
    (fun t ht x => ?_) (fun t ht x => sub_eq_zero.mpr (heq t ht x))
    (fun _ _ _ => sub_self _) hg (heatSolution_hasExpGrowthOnStrip hf hfg hν.le T)
    (fun x => by simpa only [mul_zero, heatSolution_zero] using h₀ x)
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using!
    (heatSolution_hasDerivAt_time_scaled_of_exp_growth hf.aestronglyMeasurable hfg hν ht.1 x)
      |>.hasDerivWithinAt (s := Iic t)

end MathlibExt.Analysis.PDE.HeatKernel
