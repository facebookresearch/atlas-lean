/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.SturmLiouvilleExistence
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MathlibExt.Analysis.ODE.SturmLiouvilleExistence
open MeasureTheory Set Filter Topology

/-- The Dirichlet problem `-u'' = 1`, `u 0 = u 1 = 0` is solved by the parabola
`x ↦ x * (1 - x) / 2`: we check that the solution produced by
`sturm_liouville_existence` is exactly that function. -/
example : ∃ u : ℝ → ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, u x = x * (1 - x) / 2) := by
  obtain ⟨u, huC2, hode, hu0, hu1⟩ :=
    sturm_liouville_existence 0 (by intro x; simp) 1
  have hu_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (deriv u s) s := by
    intro s hs
    have hwAt : ContDiffAt ℝ 1 u s :=
      (huC2.contDiffAt (Icc_mem_nhds hs.1 hs.2)).of_le (by norm_num)
    exact (hwAt.differentiableAt (by norm_num)).hasDerivAt
  have hd : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (deriv u) (deriv (deriv u) z) z := by
    intro z hz
    have hwAt : ContDiffAt ℝ 2 u z := huC2.contDiffAt (Icc_mem_nhds hz.1 hz.2)
    exact ((hwAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv u) x = -1 := by
    intro x hx
    have hdew : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        derivWithin u (Set.Icc (0 : ℝ) 1) y = deriv u y :=
      fun y hy => derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    have hdew2 : derivWithin (derivWithin u (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) x =
        deriv (deriv u) x := by
      have hcongr : HasDerivWithinAt (derivWithin u (Set.Icc (0 : ℝ) 1)) (deriv (deriv u) x)
          (Set.Icc (0 : ℝ) 1) x :=
        ((hd x hx).hasDerivWithinAt).congr_of_eventuallyEq
          (by filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy
            using hdew y hy)
          (hdew x hx)
      exact hcongr.derivWithin (uniqueDiffOn_Icc_zero_one x ⟨hx.1.le, hx.2.le⟩)
    have hiter : iteratedDerivWithin 2 u (Set.Icc 0 1) x =
        derivWithin (derivWithin u (Set.Icc 0 1)) (Set.Icc 0 1) x := by
      have h1 : iteratedDerivWithin 2 u (Set.Icc 0 1) =
          derivWithin (iteratedDerivWithin 1 u (Set.Icc 0 1)) (Set.Icc 0 1) :=
        iteratedDerivWithin_succ
      have h0 : iteratedDerivWithin 1 u (Set.Icc 0 1) = derivWithin u (Set.Icc 0 1) := by
        simp [iteratedDerivWithin_succ]
      rw [h1, h0]
    have hodex := hode x ⟨hx.1.le, hx.2.le⟩
    simp only [ContinuousMap.zero_apply, zero_mul, ContinuousMap.one_apply] at hodex
    rw [hiter, hdew2] at hodex
    linarith
  -- `deriv u + id` is constant on `(0, 1)`.
  have hφ : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv u x + x = deriv u y + y := by
    intro x hx y hy
    have hdiff : DifferentiableOn ℝ (fun x => deriv u x + x) (Set.Ioo (0 : ℝ) 1) := by
      intro z hz
      exact ((hd z hz).add (hasDerivAt_id z)).hasDerivWithinAt.differentiableWithinAt
    have hder0 : Set.EqOn (deriv (fun x => deriv u x + x)) 0 (Set.Ioo (0 : ℝ) 1) := by
      intro z hz
      have hderiv : HasDerivAt (fun x => deriv u x + x) (deriv (deriv u) z + 1) z :=
        (hd z hz).add (hasDerivAt_id z)
      rw [hderiv.deriv, h2 z hz]
      simp
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hder0 hx hy
  set c : ℝ := deriv u (1 / 2) + 1 / 2 with hc_def
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv u s = c - s := by
    intro s hs
    have h := hφ s hs (1 / 2) (by norm_num)
    rw [← hc_def] at h
    linarith
  -- Pin down `c = 1 / 2` from `∫₀¹ deriv u = u 1 - u 0 = 0`.
  have hInt1 : ∫ s in (0 : ℝ)..1, deriv u s = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      huC2.continuousOn hu_deriv
      ((continuous_const (y := c).sub continuous_id).intervalIntegrable 0 1 |>.congr_uIoo
        (fun s hs => by
          have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by
            rwa [Set.uIoo_of_le zero_le_one] at hs
          exact (hderiv s hs').symm))
    rw [hu1, hu0] at hFTC
    simpa using hFTC
  have hInt2 : ∫ s in (0 : ℝ)..1, deriv u s = c - 1 / 2 := by
    rw [intervalIntegral.integral_congr_uIoo (fun s hs => by
      have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by rwa [Set.uIoo_of_le zero_le_one] at hs
      exact hderiv s hs')]
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 1)
      intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    ring
  have hc : c = 1 / 2 := by linarith
  refine ⟨u, ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, hu0]
    norm_num
  · have hFTC : ∫ s in (0 : ℝ)..x, deriv u s = u x - u 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
        (huC2.continuousOn.mono (Set.Icc_subset_Icc (le_refl 0) hx.2))
        (fun s hs => hu_deriv s ⟨hs.1, lt_of_lt_of_le hs.2 hx.2⟩)
        ((continuous_const (y := (1 : ℝ) / 2).sub continuous_id).intervalIntegrable 0 x |>.congr_uIoo
          (fun s hs => by
            have hs' : s ∈ Set.Ioo (0 : ℝ) x := by rwa [Set.uIoo_of_le hx.1] at hs
            have hs'' : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs'.1, lt_of_lt_of_le hs'.2 hx.2⟩
            simp [hderiv s hs'', hc]))
    have hval : ∫ s in (0 : ℝ)..x, deriv u s = x / 2 - x ^ 2 / 2 := by
      rw [intervalIntegral.integral_congr_uIoo (fun s hs => by
        have hs' : s ∈ Set.Ioo (0 : ℝ) x := by rwa [Set.uIoo_of_le hx.1] at hs
        have hs'' : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs'.1, lt_of_lt_of_le hs'.2 hx.2⟩
        show deriv u s = 1 / 2 - s
        rw [hderiv s hs'', hc])]
      rw [intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable 0 x)
        intervalIntegral.intervalIntegrable_id,
        intervalIntegral.integral_const, integral_id]
      ring
    rw [hval, hu0] at hFTC
    have hu : u x = x / 2 - x ^ 2 / 2 := by linarith
    rw [hu]
    ring
