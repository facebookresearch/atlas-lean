/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.Tauberian

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the Tauberian theorems for power series

* Both theorems applied to the geometric series `(1 / 2) ^ n`, whose Abel
  sum is `2` (computed from the geometric series).
* The alternating series `(-1) ^ n` is Abel summable to `1 / 2`
  (`∑' (-1) ^ n * r ^ n = (1 + r)⁻¹`), but its partial sums do not converge
  to `1 / 2`: Tauber's `n * aₙ → 0` hypothesis cannot be dropped, since
  `n * (-1) ^ n` does not tend to `0`.
-/

namespace MathlibExtTest.Analysis.Series.TauberianTests

open Filter Topology Set Finset
open MathlibExt.Analysis.Series.Tauberian

/-- The geometric series `(1 / 2) ^ n` is Abel summable to `2`. -/
theorem abelSummable_geometric_half :
    Tendsto (fun r => ∑' n, (1 / 2 : ℝ) ^ n * r ^ n) (𝓝[<] 1) (𝓝 2) := by
  have hc : Tendsto (fun r : ℝ => (1 - r / 2)⁻¹) (𝓝[<] 1) (𝓝 2) := by
    have hcont : ContinuousAt (fun r : ℝ => 1 - r / 2) (1 : ℝ) := by fun_prop
    have h : ContinuousAt (fun r : ℝ => (1 - r / 2)⁻¹) (1 : ℝ) :=
      hcont.inv₀ (by norm_num)
    have h2 : Tendsto (fun r : ℝ => (1 - r / 2)⁻¹) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 - (1 : ℝ) / 2)⁻¹)) :=
      h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    rwa [show (1 - (1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h2
  have hEq : (fun r => (1 - r / 2)⁻¹) =ᶠ[𝓝[<] 1]
      (fun r => ∑' n, (1 / 2 : ℝ) ^ n * r ^ n) := by
    show ∀ᶠ r in 𝓝[<] (1 : ℝ), (1 - r / 2)⁻¹ = ∑' n, (1 / 2 : ℝ) ^ n * r ^ n
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with r hr hrl
    rw [Set.mem_Ioo] at hr
    have hnorm : ‖r / 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        div_lt_one (by norm_num : (0 : ℝ) < 2)]
      exact abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩
    have htsum : ∑' n, (1 / 2 : ℝ) ^ n * r ^ n = (1 - r / 2)⁻¹ := by
      have h1 : (fun n => (1 / 2 : ℝ) ^ n * r ^ n) = (fun n => (r / 2) ^ n) := by
        funext n
        rw [← mul_pow]
        congr 1
        ring
      rw [h1, tsum_geometric_of_norm_lt_one hnorm]
    exact htsum.symm
  exact Tendsto.congr' hEq hc

/-- Tauber's theorem applied to the geometric series. -/
theorem tauber_geometric :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) atTop (𝓝 2) :=
  tauber_tendsto_partial_sums abelSummable_geometric_half
    (tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num))

/-- Hardy–Littlewood applied to the geometric series. -/
theorem hardy_littlewood_geometric :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) atTop (𝓝 2) :=
  hardy_littlewood_tendsto_partial_sums (fun n => by positivity)
    (fun r hr => by
      rw [Set.mem_Ioo] at hr
      have h1 : (fun n => (1 / 2 : ℝ) ^ n * r ^ n) = (fun n => (r / 2) ^ n) := by
        funext n
        rw [← mul_pow]
        congr 1
        ring
      rw [h1]
      exact summable_geometric_of_lt_one (by linarith [hr.1])
        (by linarith [hr.2]))
    abelSummable_geometric_half

/-- The alternating series `(-1) ^ n` is Abel summable to `1 / 2`. -/
theorem abelSummable_alternating :
    Tendsto (fun r => ∑' n, (-1 : ℝ) ^ n * r ^ n) (𝓝[<] 1) (𝓝 (1 / 2)) := by
  have hc : Tendsto (fun r : ℝ => (1 + r)⁻¹) (𝓝[<] 1) (𝓝 (1 / 2)) := by
    have hcont : ContinuousAt (fun r : ℝ => 1 + r) (1 : ℝ) := by fun_prop
    have h : ContinuousAt (fun r : ℝ => (1 + r)⁻¹) (1 : ℝ) :=
      hcont.inv₀ (by norm_num)
    have h2 : Tendsto (fun r : ℝ => (1 + r)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 ((1 + (1 : ℝ))⁻¹)) :=
      h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    rwa [show (1 + (1 : ℝ))⁻¹ = 1 / 2 by norm_num] at h2
  have hEq : (fun r => (1 + r)⁻¹) =ᶠ[𝓝[<] 1]
      (fun r => ∑' n, (-1 : ℝ) ^ n * r ^ n) := by
    show ∀ᶠ r in 𝓝[<] (1 : ℝ), (1 + r)⁻¹ = ∑' n, (-1 : ℝ) ^ n * r ^ n
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with r hr hrl
    rw [Set.mem_Ioo] at hr
    have hnorm : ‖-r‖ < 1 := by
      rw [norm_neg, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨hr.1, hrl⟩
    have htsum : ∑' n, (-1 : ℝ) ^ n * r ^ n = (1 + r)⁻¹ := by
      have h1 : (fun n => (-1 : ℝ) ^ n * r ^ n) = (fun n => (-r) ^ n) := by
        funext n
        rw [show (-r : ℝ) = (-1) * r by ring, mul_pow]
      rw [h1, tsum_geometric_of_norm_lt_one hnorm]
      congr 1
      ring
    exact htsum.symm
  exact Tendsto.congr' hEq hc

/-- Sharpness: the partial sums of `(-1) ^ n` do not converge to `1 / 2`, so
Tauber's `n * aₙ → 0` hypothesis cannot be dropped (here `n * (-1) ^ n` does
not tend to `0`). -/
theorem not_tendsto_partial_sums_alternating :
    ¬ Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n) atTop (𝓝 (1 / 2)) := by
  intro h
  have h0 : Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (𝓝 0) := by
    have hshift : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n) atTop
        (𝓝 (1 / 2)) :=
      h.comp (tendsto_add_atTop_nat 1)
    have hdiff : Tendsto
        (fun N => (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n) -
          (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n)) atTop (𝓝 ((1 / 2 : ℝ) - 1 / 2)) :=
      hshift.sub h
    rw [sub_self] at hdiff
    have hEq : (fun N => (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n) -
        (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n)) = (fun N => (-1 : ℝ) ^ N) := by
      funext N
      rw [Finset.sum_range_succ]
      ring
    rwa [hEq] at hdiff
  have h1 := h0.norm
  rw [norm_zero] at h1
  simp only [norm_pow, norm_neg, norm_one, one_pow] at h1
  have hcontra : (0 : ℝ) = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
  exact zero_ne_one hcontra

end MathlibExtTest.Analysis.Series.TauberianTests
