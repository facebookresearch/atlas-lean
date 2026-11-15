/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.EarthScience.WeakDiffusionOnInterval

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weak diffusion on `(0, 1)`: witness, energy identity, degenerate case

Concrete consumers of `PhyslibExt.EarthScience.WeakDiffusionOnInterval`:
for `kappa = 1`, `f = 2` the weak solution has value `1 / 4` at `1 / 2`
(the parabola `x * (1 - x)`), vanishes at both endpoints, and satisfies
the energy identity `∫ (u')² = ∫ 2 * u`; for `f = 0` the solution is zero.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The parabola profile as an H¹₀ function
- B. The `kappa = 1`, `f = 2` solution: value, endpoints, energy
- C. The degenerate `f = 0` case: zero solution

## iv. References

- `PhyslibExt.EarthScience.WeakDiffusionOnInterval`
-/

open MeasureTheory

/-- The primitive of `1 - 2 * t` is `x - x ^ 2`. -/
private theorem parabola_integral (x : ℝ) :
    (∫ t in (0 : ℝ)..x, (1 - 2 * t)) = x - x ^ 2 := by
  have h1 : (∫ t in (0 : ℝ)..x, (1 : ℝ)) = x := by
    rw [intervalIntegral.integral_const]
    simp
  have h2 : (∫ t in (0 : ℝ)..x, (2 * t)) = x ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hInt2 : IntervalIntegrable (fun t : ℝ => 2 * t) volume 0 x :=
    (continuous_const.mul continuous_id').intervalIntegrable 0 x
  have hsub := (intervalIntegral.integral_sub (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => 2 * t)
    intervalIntegrable_const hInt2).symm
  rw [← hsub, h1, h2]

/-- The parabola `x * (1 - x)` as an H¹₀(0, 1) function, with weak
derivative `1 - 2 * x`. -/
private noncomputable def parabolaWeakH10 : EarthScience.WeakH10 where
  toFun := fun x => x * (1 - x)
  weakDeriv := fun x => 1 - 2 * x
  weakDeriv_memLp :=
    MemLp.of_bound
      (continuous_const.sub (continuous_const.mul continuous_id')).aestronglyMeasurable 1
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩)
  toFun_eq_integral := by
    intro x hx
    rw [parabola_integral]
    ring
  integral_weakDeriv_eq_zero := by
    rw [parabola_integral]
    norm_num

/-- The parabola satisfies the weak equation for `kappa = 1`, `f = 2`. -/
private theorem parabola_is_solution (v : EarthScience.WeakH10) :
    (∫ x in (0 : ℝ)..1, 1 * parabolaWeakH10.weakDeriv x * v.weakDeriv x)
      = ∫ x in (0 : ℝ)..1, 2 * v.toFun x := by
  have hconv : ∀ h : ℝ → ℝ,
      (∫ x in (0 : ℝ)..1, h x) = ∫ x, h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro h
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv, hconv]
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
  have hg_int : Integrable v.weakDeriv μ := by
    have h1 : MemLp v.weakDeriv 1 μ := v.weakDeriv_memLp.mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have h1 : (∫ x, 1 * v.weakDeriv x ∂μ) = 0 := by
    have h : (∫ x, v.weakDeriv x ∂μ) = 0 := by
      rw [← hconv]
      exact v.integral_weakDeriv_eq_zero
    rw [← h]
    apply integral_congr_ae
    filter_upwards with x
    simp
  have hφmeas : AEStronglyMeasurable (fun x : ℝ => 2 * x) μ := by
    rw [hμdef]
    exact (continuous_const.mul continuous_id').continuousOn.aestronglyMeasurable
      measurableSet_Icc
  have hφbdd : ∀ᵐ x ∂μ, ‖(fun x : ℝ => 2 * x) x‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs]
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    calc |2 * x| = 2 * |x| := by rw [abs_mul]; norm_num
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hx1 (by norm_num)
      _ = 2 := by norm_num
  have h2int : Integrable (fun x => (2 * x) * v.weakDeriv x) μ :=
    hg_int.bdd_mul hφmeas hφbdd
  have hsplit : (∫ x, (1 - 2 * x) * v.weakDeriv x ∂μ)
      = (∫ x, 1 * v.weakDeriv x ∂μ) - ∫ x, (2 * x) * v.weakDeriv x ∂μ := by
    have hsub := integral_sub (hg_int.const_mul 1) h2int
    rw [← hsub]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have h2 : (∫ x, (2 * x) * v.weakDeriv x ∂μ)
      = -2 * ∫ x, v.toFun x ∂μ := by
    have hFub := EarthScience.integral_primitive_mul_eq_neg
      (f := fun _ : ℝ => (2 : ℝ)) (g := v.weakDeriv) (V := v.toFun)
      (MemLp.of_bound aestronglyMeasurable_const 2
        (Filter.Eventually.of_forall fun _ => by simp))
      v.weakDeriv_memLp v.toFun_eq_integral v.integral_weakDeriv_eq_zero
    have hprim : ∀ x : ℝ, (∫ t in (0 : ℝ)..x, (2 : ℝ)) = 2 * x := by
      intro x
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring
    have hstep : (∫ x, (2 * x) * v.weakDeriv x ∂μ)
        = ∫ x, (∫ t in (0 : ℝ)..x, (2 : ℝ)) * v.weakDeriv x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hprim x]
    rw [hstep, hFub, integral_const_mul]
    ring
  have hLHS : (∫ x, 1 * parabolaWeakH10.weakDeriv x * v.weakDeriv x ∂μ)
      = ∫ x, (1 - 2 * x) * v.weakDeriv x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    show (1 * parabolaWeakH10.weakDeriv x * v.weakDeriv x)
      = (1 - 2 * x) * v.weakDeriv x
    rw [show parabolaWeakH10.weakDeriv x = 1 - 2 * x from rfl]
    ring
  rw [hLHS, hsplit, h1, h2]
  rw [integral_const_mul]
  ring

/-- The zero H¹₀ function. -/
private noncomputable def zeroWeakH10 : EarthScience.WeakH10 where
  toFun := fun _ => 0
  weakDeriv := fun _ => 0
  weakDeriv_memLp := MemLp.of_bound aestronglyMeasurable_const 0
    (Filter.Eventually.of_forall fun _ => by simp)
  toFun_eq_integral := by
    intro x _
    simp
  integral_weakDeriv_eq_zero := by
    simp

/-- For `kappa = 1`, `f = 2`: the weak solution has value `1 / 4` at
`1 / 2` and vanishes at both endpoints. -/
example : ∃ u : EarthScience.WeakH10,
    u.toFun 0 = 0 ∧ u.toFun 1 = 0 ∧ u.toFun (1 / 2) = 1 / 4 := by
  obtain ⟨u, hu_eq, hu_uniq⟩ := EarthScience.weak_diffusion_exists_unique
    (κ := fun _ : ℝ => (1 : ℝ)) (f := fun _ : ℝ => (2 : ℝ)) (kmin := 1) (kmax := 1)
    (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    (MemLp.of_bound aestronglyMeasurable_const 2
      (Filter.Eventually.of_forall fun _ => by simp))
  refine ⟨u, ?_, ?_, ?_⟩
  · exact (EarthScience.weakH10_endpoints u).1
  · exact (EarthScience.weakH10_endpoints u).2
  · have hEq := hu_uniq parabolaWeakH10 parabola_is_solution
    have h := hEq (show (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
    simp [parabolaWeakH10] at h
    calc u.toFun (1 / 2) = u.toFun 2⁻¹ := by congr 1; norm_num
      _ = 1 / 4 := by rw [← h]; norm_num

/-- For `kappa = 1`, `f = 2`: the energy identity `∫ (u')² = ∫ 2 * u`. -/
example : ∃ u : EarthScience.WeakH10,
    (∫ x in (0 : ℝ)..1, (u.weakDeriv x) ^ 2)
      = ∫ x in (0 : ℝ)..1, 2 * u.toFun x := by
  obtain ⟨u, hu_eq, -⟩ := EarthScience.weak_diffusion_exists_unique
    (κ := fun _ : ℝ => (1 : ℝ)) (f := fun _ : ℝ => (2 : ℝ)) (kmin := 1) (kmax := 1)
    (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    (MemLp.of_bound aestronglyMeasurable_const 2
      (Filter.Eventually.of_forall fun _ => by simp))
  refine ⟨u, ?_⟩
  have h := hu_eq u
  have hLHS : (∫ x in (0 : ℝ)..1, 1 * u.weakDeriv x * u.weakDeriv x)
      = ∫ x in (0 : ℝ)..1, (u.weakDeriv x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    simp [sq]
  rw [hLHS] at h
  exact h

/-- Degenerate case `f = 0`: the weak solution is zero on `[0, 1]`. -/
example : ∃ u : EarthScience.WeakH10, ∀ x ∈ Set.Icc (0 : ℝ) 1, u.toFun x = 0 := by
  obtain ⟨u, -, hu_uniq⟩ := EarthScience.weak_diffusion_exists_unique
    (κ := fun _ : ℝ => (1 : ℝ)) (f := fun _ : ℝ => (0 : ℝ)) (kmin := 1) (kmax := 1)
    (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    (MemLp.of_bound aestronglyMeasurable_const 0
      (Filter.Eventually.of_forall fun _ => by simp))
  refine ⟨u, fun x hx => ?_⟩
  have hzero : ∀ v : EarthScience.WeakH10,
      (∫ x in (0 : ℝ)..1, 1 * zeroWeakH10.weakDeriv x * v.weakDeriv x)
        = ∫ x in (0 : ℝ)..1, 0 * v.toFun x := by
    intro v
    simp [zeroWeakH10]
  have hEq := hu_uniq zeroWeakH10 hzero
  have h := hEq hx
  exact h.symm
