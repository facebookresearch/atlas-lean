/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Summable families under Gaussian and Duhamel integrals

A common exponential spatial weight and summable nonnegative amplitudes justify
interchanging a series with the whole-line Gaussian and its finite-time
Duhamel integral. This is the dominated convergence argument used in Volterra
constructions of potential-heat solutions.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- Summable amplitudes with a common exponential spatial weight allow a series
to pass through heat evolution. The data may be merely measurable. -/
theorem heatSolution_hasSum_of_exp_bound {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℝ} {A : ι → ℝ} {c : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n))
    (hAs : Summable A) (hc : 0 ≤ c) (hb : ∀ n y, |f n y| ≤ A n * exp (c * |y|))
    (t x : ℝ) :
    HasSum (fun n => heatSolution (f n) t x)
      (heatSolution (fun y => ∑' n, f n y) t x) := by
  have hs (y : ℝ) : HasSum (fun n => f n y) (∑' n, f n y) := by
    apply Summable.hasSum
    apply (hAs.mul_right (exp (c * |y|))).of_norm_bounded
    intro n
    simpa only [Real.norm_eq_abs] using hb n y
  by_cases ht : 0 < t
  · simp_rw [heatSolution_of_pos _ ht]
    let B := fun y => heatKernel ℝ t (x-y) * exp (c * |y|)
    have hB : Integrable B :=
      integrable_heatKernel_mul_of_exp_growth (by fun_prop)
        ⟨1,c,by norm_num,hc,fun y => by simp [abs_of_pos (exp_pos _)]⟩ ht x
    apply MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun n y => A n * B y) ?_ ?_ ?_ ?_ ?_
    · intro n
      simpa only [Pi.mul_apply] using!
        (((heatKernel_contDiff t).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable.mul (hf n))
    · intro n
      filter_upwards with y
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (heatKernel_pos ht (x-y))]
      calc
        _ ≤ heatKernel ℝ t (x-y) * (A n * exp (c*|y|)) :=
          mul_le_mul_of_nonneg_left (hb n y) (heatKernel_pos ht _).le
        _ = _ := by dsimp only [B]; ring
    · filter_upwards with y
      exact hAs.mul_right (B y)
    · simp_rw [tsum_mul_right]
      exact hB.const_mul _
    · filter_upwards with y
      exact (hs y).mul_left _
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hs x

/-- A jointly continuous family with summable uniform exponential amplitudes
may be summed under the actual finite-time Duhamel integral. -/
theorem heatDuhamel_hasSum_of_exp_bound {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℝ → ℝ} {A : ι → ℝ} {T c ν t : ℝ}
    (hf : ∀ n, ContinuousOn (Function.uncurry (f n)) (Icc 0 T ×ˢ univ))
    (hA : ∀ n, 0 ≤ A n) (hAs : Summable A) (hc : 0 ≤ c)
    (hb : ∀ n s, s ∈ Icc 0 T → ∀ y, |f n s y| ≤ A n * exp (c * |y|))
    (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasSum (fun n => heatDuhamel ν (f n) t x)
      (heatDuhamel ν (fun s y => ∑' n, f n s y) t x) := by
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hslice (n : ι) (s : ℝ) (hs : s ∈ Icc 0 T) : Continuous (f n s) :=
    (hf n).comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨hs,mem_univ y⟩)
  unfold heatDuhamel
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => A n * J * exp (c * |x|)) ?_ ?_ ?_ ?_ ?_
  · intro n
    simpa only [uIoc_of_le ht.1] using
      (intervalIntegrable_heatDuhamel (hf n) ⟨A n,c,hA n,hc,hb n⟩ ν ht x).1.aestronglyMeasurable
  · intro n
    filter_upwards with s
    intro hs
    have hs' : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht.1] using hs
    have hsT : s ∈ Icc 0 T := ⟨hs'.1.le,hs'.2.trans ht.2⟩
    simpa only [Real.norm_eq_abs] using abs_heatSolution_le_exp_bound (hslice n s hsT)
      (hA n) hc (hb n s hsT)
      (mul_le_mul_of_nonneg_left ((sub_le_self t hs'.1.le).trans ht.2) hν) x
  · filter_upwards with s _
    exact (hAs.mul_right J).mul_right _
  · exact intervalIntegrable_const
  · filter_upwards with s
    intro hs
    have hs' : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht.1] using hs
    have hsT : s ∈ Icc 0 T := ⟨hs'.1.le,hs'.2.trans ht.2⟩
    exact heatSolution_hasSum_of_exp_bound (fun n => (hslice n s hsT).aestronglyMeasurable)
      hAs hc (fun n => hb n s hsT) _ x

end MathlibExt.Analysis.PDE.HeatKernel
