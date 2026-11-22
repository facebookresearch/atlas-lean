/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersFiniteTime
import MathlibExt.Analysis.PDE.BurgersStability
import Mathlib.Tactic.FunProp

open MeasureTheory ColeHopf

example {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (hi : Integrable (fun x => u x - v x))
    (a : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν u a t x - burgersSolution ν v a t x) ∧
      (∫ x, |burgersSolution ν u a t x - burgersSolution ν v a t x|) ≤ ∫ x, |u x - v x| :=
  burgersSolution_l1_contraction hu hv hbu hbv hν hi a ht

open Real Filter

private noncomputable def wave (x : ℝ) : ℝ := exp (-x ^ 2) * sin x

private theorem wave_continuous : Continuous wave := by unfold wave; fun_prop

private theorem wave_dominated (x : ℝ) : |wave x| ≤ exp (-x ^ 2) := by
  rw [wave, abs_mul, abs_of_pos (exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_sin_le_one x) (exp_pos _).le

private theorem wave_bound (x : ℝ) : |wave x| ≤ 1 :=
  (wave_dominated x).trans (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x)))

private theorem wave_integrable : Integrable wave := by
  have hg : Integrable (fun x : ℝ => exp (-x ^ 2)) := by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  exact hg.mono' wave_continuous.aestronglyMeasurable (ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs] using wave_dominated x))

-- A signed integrable perturbation of a nonzero constant background.
example (a b t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution 3 (fun y => 2 + wave y) a t x -
      burgersSolution 3 (fun _ => 2) b t x) ∧
    (∫ x, |burgersSolution 3 (fun y => 2 + wave y) a t x -
      burgersSolution 3 (fun _ => 2) b t x|) ≤ ∫ x, |wave x| := by
  have hb (x : ℝ) : |2 + wave x| ≤ 3 := by
    have h := norm_add_le (2 : ℝ) (wave x)
    simp only [Real.norm_eq_abs] at h
    norm_num at h
    linarith [wave_bound x]
  have hi : Integrable (fun x => (2 + wave x) - 2) := by
    simpa only [add_sub_cancel_left] using wave_integrable
  simpa only [add_sub_cancel_left] using burgersSolution_l1_contraction_of_anchors
    (show Continuous (fun x => 2 + wave x) from continuous_const.add wave_continuous)
    continuous_const ⟨3, hb⟩ ⟨2, by intro x; norm_num⟩ (by norm_num) hi a b ht

-- The ordered case also accepts a nondifferentiable localized perturbation.
example (a t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution (1 / 100) (fun y => |wave y|) a t x -
      burgersSolution (1 / 100) (fun _ => 0) a t x) ∧
    (∫ x, burgersSolution (1 / 100) (fun y => |wave y|) a t x -
      burgersSolution (1 / 100) (fun _ => 0) a t x) ≤ ∫ x, |wave x| := by
  simpa only [sub_zero] using burgersSolution_ordered_integral_le
    (show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const)
    (show Continuous (fun y => |wave y|) from wave_continuous.abs)
    ⟨0, by intros; simp⟩ ⟨1, fun y => by simpa only [abs_abs] using wave_bound y⟩
    (by norm_num : (0 : ℝ) < 1 / 100) (fun y => abs_nonneg (wave y))
    (by simpa only [sub_zero] using! wave_integrable.abs) a ht

-- Initial-time contraction is equality and permits unrelated anchors.
example (a b : ℝ) :
    (∫ x, |burgersSolution 3 wave a 0 x - burgersSolution 3 (fun _ => 0) b 0 x|) =
      ∫ x, |wave x| := by
  simp only [burgersSolution_zero wave_continuous (by norm_num : (3 : ℝ) ≠ 0),
    burgersSolution_zero continuous_const (by norm_num : (3 : ℝ) ≠ 0), sub_zero]

example : 0 < wave (π / 2) ∧ wave (-(π / 2)) < 0 := by
  simp only [wave, sin_pi_div_two, sin_neg, mul_one, mul_neg, neg_lt_zero]
  exact ⟨exp_pos _, exp_pos _⟩

-- Only differences, not the individual velocities, need to be integrable.
example : ¬ Integrable (fun _ : ℝ => (2 : ℝ)) := by
  intro h
  have : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (2 : ℝ) ≠ 0)).mp h
  have hfin := measure_lt_top (volume : Measure ℝ) Set.univ
  rw [Real.volume_univ] at hfin
  exact (lt_irrefl _ hfin)

-- Contraction can be restarted from a positive-time slice.
example {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    (hi : Integrable (fun x => u x - v x)) (a : ℝ) :
    (∫ x, |burgersSolution 3 u a 3 x - burgersSolution 3 v a 3 x|) ≤
      ∫ x, |burgersSolution 3 u a 1 x - burgersSolution 3 v a 1 x| := by
  have hν : (0 : ℝ) < 3 := by norm_num
  have hcu : Continuous (burgersSolution 3 u a 1) :=
    (burgersSolution_continuous_of_bounded hu hbu hν a).comp
      (continuous_const.prodMk continuous_id)
  have hcv : Continuous (burgersSolution 3 v a 1) :=
    (burgersSolution_continuous_of_bounded hv hbv hν a).comp
      (continuous_const.prodMk continuous_id)
  have hbu' : ∃ M, ∀ x, |burgersSolution 3 u a 1 x| ≤ M := by
    obtain ⟨M, hM⟩ := hbu
    exact ⟨M, fun x => abs_burgersSolution_le hu hν hM a 1 x⟩
  have hbv' : ∃ M, ∀ x, |burgersSolution 3 v a 1 x| ≤ M := by
    obtain ⟨M, hM⟩ := hbv
    exact ⟨M, fun x => abs_burgersSolution_le hv hν hM a 1 x⟩
  have hi' := (burgersSolution_l1_contraction hu hv hbu hbv hν hi a (by norm_num : (0 : ℝ) ≤ 1)).1
  have hh := (burgersSolution_l1_contraction hcu hcv hbu' hbv' hν hi' a
    (by norm_num : (0 : ℝ) ≤ 2)).2
  simp_rw [burgersSolution_restart hu hbu hν a a 1 2 _ (by norm_num) (by norm_num),
    burgersSolution_restart hv hbv hν a a 1 2 _ (by norm_num) (by norm_num)] at hh
  norm_num at hh ⊢
  exact hh

open Set
open scoped ContDiff

-- The complete theory transfers stability to finite-lifespan classical competitors.
example {u v : ℝ → ℝ → ℝ} {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Ioo 0 T ×ˢ univ))
    (hbu : ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |u s x| ≤ M)
    (hbv : ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |v s x| ≤ M)
    (hpu : ∀ s ∈ Ioo 0 T, ∀ x,
      deriv (fun r => u r x) s + u s x * deriv (u s) x = ν * iteratedDeriv 2 (u s) x)
    (hpv : ∀ s ∈ Ioo 0 T, ∀ x,
      deriv (fun r => v r x) s + v s x * deriv (v s) x = ν * iteratedDeriv 2 (v s) x)
    (hi : Integrable (fun x => u 0 x - v 0 x)) :
    Integrable (fun x => u t x - v t x) ∧
      (∫ x, |u t x - v t x|) ≤ ∫ x, |u 0 x - v 0 x| := by
  have hc0u : Continuous (u 0) := by
    rw [← continuousOn_univ]
    exact hcu.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hx => ⟨⟨le_rfl, ht.1.trans ht.2⟩, hx⟩)
  have hc0v : Continuous (v 0) := by
    rw [← continuousOn_univ]
    exact hcv.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hx => ⟨⟨le_rfl, ht.1.trans ht.2⟩, hx⟩)
  have hb0u : ∃ M, ∀ x, |u 0 x| ≤ M := by
    obtain ⟨M, hM⟩ := hbu
    exact ⟨M, hM 0 ⟨le_rfl, ht.1.trans ht.2⟩⟩
  have hb0v : ∃ M, ∀ x, |v 0 x| ≤ M := by
    obtain ⟨M, hM⟩ := hbv
    exact ⟨M, hM 0 ⟨le_rfl, ht.1.trans ht.2⟩⟩
  simp_rw [eq_burgersSolution_finite hν hcu hu hbu hpu 0 t ht,
    eq_burgersSolution_finite hν hcv hv hbv hpv 0 t ht]
  exact burgersSolution_l1_contraction hc0u hc0v hb0u hb0v hν hi 0 ht.1
