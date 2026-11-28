/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues

@[expose] public section

/-!
# The dilogarithm power series

`Real.li2PowerSeries` is the power-series form of the dilogarithm,
`∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ 2`. It agrees with the standard real
`Li₂` on `[-1, 1]`, where the series converges. It is not an analytic
continuation: outside the convergence domain, `tsum` totalization gives `0`.
The defining identity below holds for all real inputs; the analytic results are restricted to the
indicated parts of the convergence interval.

## Main results

* `Real.li2PowerSeries_zero`, `Real.li2PowerSeries_one`: the values at `0`
  and `1`, namely `0` and `π² / 6`.
* `Real.continuousOn_li2PowerSeries`: continuity on `[-1, 1]` by the
  Weierstrass M-test with majorant `∑ 1 / (n + 1)²`.
* `Real.hasDerivAt_li2PowerSeries`: the derivative is `-log (1 - z) / z`
  for `0 < |z| < 1`; `Real.hasDerivAt_li2PowerSeries_tsum` gives the
  termwise-series derivative on all of `(-1, 1)`, including at `0`.
* `Real.li2PowerSeries_reflection`: Euler's reflection formula on `(0, 1)`.

The series definition matches `chapter9Entry8Dilog` of
`MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry8Arcsin`, which is now defined
through `Real.li2PowerSeries`.
-/

open Filter Set
open scoped Topology

namespace Real

/-- The dilogarithm power series
`∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ 2`. On `[-1, 1]` this is the standard
real dilogarithm `Li₂`; outside that interval this totalized series is not
an analytic continuation (`tsum` gives `0` where the series is not summable). -/
noncomputable def li2PowerSeries (z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2

/-- With the denominator written using real addition, the totalized dilogarithm power series at
`z : ℝ` is $\sum_{n=0}^{\infty} z^{n+1}/(n+1)^2$, interpreted as `0` when the series is not
summable. -/
theorem li2PowerSeries_eq_tsum (z : ℝ) :
    li2PowerSeries z = ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  simp only [li2PowerSeries, Nat.cast_add, Nat.cast_one]

private theorem summable_li2PowerSeries_term_of_abs_lt_one {z : ℝ} (hz : |z| < 1) :
    Summable (fun n : ℕ => z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2) := by
  have hax : |(|z|)| < 1 := by rwa [abs_abs]
  have hgeo : Summable (fun n : ℕ => |z| ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_abs_lt_one hax).mul_right |z|
  refine Summable.of_norm_bounded hgeo fun n => ?_
  have h1 : (1 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have h2 : (1 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) ^ 2 := one_le_pow₀ h1
  have hnn : (0 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have habs : |(((n + 1 : ℕ)) : ℝ)| = (((n + 1 : ℕ)) : ℝ) := abs_of_nonneg hnn
  simp only [norm_div, norm_pow, Real.norm_eq_abs, habs]
  exact div_le_self (by positivity) h2

/-- The defining series converges to `li2PowerSeries z` for `|z| < 1`. -/
theorem hasSum_li2PowerSeries {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2) (li2PowerSeries z) :=
  (summable_li2PowerSeries_term_of_abs_lt_one hz).hasSum

/-- `Li₂(0) = 0`. -/
theorem li2PowerSeries_zero : li2PowerSeries 0 = 0 := by
  have h : ∀ n : ℕ, (0 : ℝ) ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2 = 0 :=
    fun n => by rw [zero_pow (by omega : n + 1 ≠ 0), zero_div]
  simp only [li2PowerSeries, h, tsum_zero]

private theorem hasSum_one_div_add_one_sq_cast :
    HasSum (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2) (π ^ 2 / 6) :=
  (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
    (by simpa using hasSum_zeta_two)

/-- The Basel value `Li₂(1) = π² / 6`. -/
theorem li2PowerSeries_one : li2PowerSeries 1 = π ^ 2 / 6 := by
  have h := hasSum_one_div_add_one_sq_cast.tsum_eq
  rw [li2PowerSeries]
  simpa only [one_pow] using h

/-- `li2PowerSeries` is continuous on `[-1, 1]`, by the Weierstrass M-test
against the convergent majorant `∑ 1 / (n + 1)²`. -/
theorem continuousOn_li2PowerSeries : ContinuousOn li2PowerSeries (Set.Icc (-1) 1) := by
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Icc (-1) 1,
      ‖z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2‖ ≤ (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2 := by
    intro n z hz
    have hz1 : |z| ≤ 1 := abs_le.mpr hz
    have hz0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have hc : (0 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
    simp only [norm_div, norm_pow, Real.norm_eq_abs, abs_of_nonneg hc]
    exact div_le_div_of_nonneg_right (pow_le_one₀ hz0 hz1) (pow_nonneg hc 2)
  have hU : TendstoUniformlyOn
      (fun (s : Finset ℕ) z => ∑ n ∈ s, z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2)
      (fun z => ∑' n : ℕ, z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2)
      Filter.atTop (Set.Icc (-1) 1) :=
    tendstoUniformlyOn_tsum hasSum_one_div_add_one_sq_cast.summable hbound
  have hcont : ContinuousOn (fun z => ∑' n : ℕ, z ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2)
      (Set.Icc (-1) 1) :=
    hU.continuousOn ((Filter.Eventually.of_forall fun s =>
      continuousOn_finsetSum s fun n _ => (continuousOn_id.pow _).div_const _).frequently)
  exact hcont

/-- `li2PowerSeries` is continuous at `0`. -/
theorem continuousAt_li2PowerSeries_zero : ContinuousAt li2PowerSeries 0 :=
  continuousOn_li2PowerSeries.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

private theorem tendsto_li2PowerSeries_nhdsLT_one :
    Tendsto li2PowerSeries (𝓝[<] (1 : ℝ)) (𝓝 (π ^ 2 / 6)) := by
  have h1 : Tendsto li2PowerSeries (𝓝[Set.Icc (-1) 1] (1 : ℝ)) (𝓝 (li2PowerSeries 1)) :=
    continuousOn_li2PowerSeries.continuousWithinAt (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1)
  rw [li2PowerSeries_one] at h1
  refine h1.mono_left ?_
  refine nhdsWithin_le_of_mem ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds zero_lt_one)]
    with z hz1 hz0
  exact ⟨by linarith, hz1.le⟩

/-- The termwise derivative of the defining series for `Li₂`, valid on all of
`(-1, 1)`, including at `0`. -/
theorem hasDerivAt_li2PowerSeries_tsum {z : ℝ} (hz : |z| < 1) :
    HasDerivAt li2PowerSeries (∑' n : ℕ, z ^ n / (((n + 1 : ℕ)) : ℝ)) z := by
  obtain ⟨R, hzR, hR1⟩ : ∃ R : ℝ, |z| < R ∧ R < 1 := exists_between hz
  have hR0 : (0 : ℝ) < R := (abs_nonneg z).trans_lt hzR
  have hmem : z ∈ Set.Ioo (-R) R := Set.mem_Ioo.mpr (abs_lt.mp hzR)
  have hsumv : Summable (fun n : ℕ => R ^ n) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hR0])
  have hderiv1 : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      HasDerivAt (fun x => x ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2))
        (y ^ n / (((n + 1 : ℕ)) : ℝ)) y := by
    intro n y _
    have hD : (((n + 1 : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := ((hasDerivAt_id' y).pow (n + 1)).div_const
      ((((n + 1 : ℕ)) : ℝ) ^ 2)
    simp only [Pi.pow_apply] at h1
    rw [Nat.add_sub_cancel] at h1
    have hval : (↑(n + 1) * y ^ n * 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2)
        = y ^ n / (((n + 1 : ℕ)) : ℝ) := by field_simp
    rw [hval] at h1
    exact h1
  have hbound : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      ‖y ^ n / (((n + 1 : ℕ)) : ℝ)‖ ≤ R ^ n := by
    intro n y hy
    have hyR : |y| ≤ R := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hy))
    have hD1 : (1 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hnn : (0 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
    have hDn : ‖(((n + 1 : ℕ)) : ℝ)‖ = (((n + 1 : ℕ)) : ℝ) := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg hnn
    have hYp : |y| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg _) hyR n
    simp only [norm_div, norm_pow, Real.norm_eq_abs, hDn]
    calc |y| ^ n / (((n + 1 : ℕ)) : ℝ) ≤ R ^ n / (((n + 1 : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_right hYp hnn
      _ ≤ R ^ n := div_le_self (by positivity) hD1
  have hsum0 : Summable (fun n : ℕ => z ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    summable_li2PowerSeries_term_of_abs_lt_one hz
  have hmain := hasDerivAt_tsum_of_isPreconnected hsumv isOpen_Ioo
    (convex_Ioo (-R) R).isPreconnected hderiv1 hbound hmem hsum0 hmem
  exact hmain

private theorem tsum_pow_div_eq_neg_log_div {z : ℝ} (hz : |z| < 1) (hz0 : z ≠ 0) :
    (∑' n : ℕ, z ^ n / (((n + 1 : ℕ)) : ℝ)) = -log (1 - z) / z := by
  have h := (hasSum_pow_div_log_of_abs_lt_one hz).tsum_eq
  have hcast : ∀ n : ℕ, z ^ n / (((n + 1 : ℕ)) : ℝ) =
      z⁻¹ * (z ^ (n + 1) / ((n : ℝ) + 1)) := by
    intro n
    rw [pow_succ]
    push_cast
    field_simp
  rw [tsum_congr hcast, tsum_mul_left, h, div_eq_inv_mul]

/-- The derivative of the dilogarithm power series:
`Li₂'(z) = -log (1 - z) / z` for `0 < |z| < 1`. -/
theorem hasDerivAt_li2PowerSeries {z : ℝ} (hz : |z| < 1) (hz0 : z ≠ 0) :
    HasDerivAt li2PowerSeries (-log (1 - z) / z) z := by
  rw [← tsum_pow_div_eq_neg_log_div hz hz0]
  exact hasDerivAt_li2PowerSeries_tsum hz

private theorem negMulLog_one_sub (x : ℝ) : (1 - x) * log (1 - x) =
    -negMulLog (1 - x) := by
  simp only [negMulLog]
  ring

private theorem tendsto_one_sub_mul_log_one_sub_nhdsLT_one :
    Tendsto (fun x => (1 - x) * log (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hsub : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
      (continuous_const.sub continuous_id).tendsto (1 : ℝ)
    have h' : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 : ℝ) - 1)) :=
      h.mono_left nhdsWithin_le_nhds
    simpa using h'
  have h0 : negMulLog (0 : ℝ) = 0 := by simp [negMulLog]
  have h2 : Tendsto (fun x => negMulLog (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h3 : Tendsto (fun x => negMulLog (1 - x)) (𝓝[<] (1 : ℝ))
        (𝓝 (negMulLog 0)) :=
      (continuous_negMulLog.tendsto 0).comp hsub
    rwa [h0] at h3
  have h1 : Tendsto (fun x => -negMulLog (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa using h2.neg
  exact h1.congr (fun x => (negMulLog_one_sub x).symm)

private theorem tendsto_log_div_one_sub_nhdsLT_one :
    Tendsto (fun y => log y / (1 - y)) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := by
  have h := (Real.hasDerivAt_log (one_ne_zero)).tendsto_slope
  have h2 : Tendsto (slope log 1) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hh := h.mono_left (nhdsWithin_mono (1 : ℝ) (s := Set.Iio (1 : ℝ))
      (fun z hz => ne_of_lt hz))
    simpa using hh
  have h3 : Tendsto (fun y => -(slope log 1 y)) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := h2.neg
  refine h3.congr (fun y => ?_)
  by_cases hy1 : y = 1
  · subst hy1
    simp [slope]
  · rw [slope_def_field, log_one, sub_zero, ← div_neg, neg_sub]

/-- **Euler's reflection formula for the dilogarithm**: for `z ∈ (0, 1)`,
`Li₂(z) + Li₂(1 - z) = π² / 6 - log z * log (1 - z)`. The left side plus the log
product has derivative `0` on `(0, 1)` and tends to `Li₂(1) = π² / 6` as
`z → 1⁻`. -/
theorem li2PowerSeries_reflection {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    li2PowerSeries z + li2PowerSeries (1 - z) = π ^ 2 / 6 - log z * log (1 - z) := by
  have hS : ∀ w ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun w => li2PowerSeries w + li2PowerSeries (1 - w) +
        log w * log (1 - w)) 0 w := by
    intro w hw
    have hw0 : w ≠ 0 := hw.1.ne'
    have h1w : (1 : ℝ) - w ≠ 0 := (sub_pos.mpr hw.2).ne'
    have habs : |(1 : ℝ) - w| < 1 := by
      rw [abs_of_pos (sub_pos.mpr hw.2)]
      exact sub_lt_self 1 hw.1
    have h1mx : HasDerivAt (fun w : ℝ => 1 - w) (-1) w := by
      have h := (hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id' w)
      apply h.congr_deriv
      simp
    have hcomp : HasDerivAt (fun w => li2PowerSeries (1 - w)) (log w / (1 - w)) w := by
      have h := (hasDerivAt_li2PowerSeries habs h1w).comp w h1mx
      refine h.congr_deriv ?_
      have e : (1 : ℝ) - (1 - w) = w := by ring
      rw [e]
      field_simp
    have hlog1w : HasDerivAt (fun w => log (1 - w)) (-(1 - w)⁻¹) w := by
      have h := (Real.hasDerivAt_log h1w).comp w h1mx
      refine h.congr_deriv ?_
      simp
    have h3 : HasDerivAt (fun w => log w * log (1 - w))
        (w⁻¹ * log (1 - w) + log w * (-(1 - w)⁻¹)) w :=
      (Real.hasDerivAt_log hw0).mul hlog1w
    have hli2w : HasDerivAt li2PowerSeries (-log (1 - w) / w) w :=
      hasDerivAt_li2PowerSeries (by rw [abs_of_pos hw.1]; exact hw.2) hw0
    refine (((hli2w).add hcomp).add h3).congr_deriv ?_
    field_simp
    ring
  have hconst : ∀ w ∈ Set.Ioo (0 : ℝ) 1,
      li2PowerSeries w + li2PowerSeries (1 - w) + log w * log (1 - w) =
        li2PowerSeries (1 / 2) + li2PowerSeries (1 - 1 / 2) + log (1 / 2) * log (1 - 1 / 2) := by
    intro w hw
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1 : ℝ) / 2)
      (b := w)
      (f := fun w => li2PowerSeries w + li2PowerSeries (1 - w) + log w * log (1 - w))
      (f' := fun _ => (0 : ℝ)) ?_ intervalIntegrable_const
    · rw [intervalIntegral.integral_zero] at h
      change (0 : ℝ) = (li2PowerSeries w + li2PowerSeries (1 - w) + log w * log (1 - w)) -
        (li2PowerSeries (1 / 2) + li2PowerSeries (1 - 1 / 2) + log (1 / 2) * log (1 - 1 / 2)) at h
      linarith [h]
    · intro x hx
      refine hS x ?_
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        constructor <;> linarith [hw.1, hw.2]
  have hlim : Tendsto (fun w => li2PowerSeries w + li2PowerSeries (1 - w) + log w * log (1 - w))
      (𝓝[<] (1 : ℝ)) (𝓝 (π ^ 2 / 6)) := by
    have hcomp : Tendsto (fun w => li2PowerSeries (1 - w)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hmap : Tendsto (fun w : ℝ => 1 - w) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h : Tendsto (fun w : ℝ => (1 : ℝ) - w) (𝓝[<] (1 : ℝ))
              (𝓝 ((1 : ℝ) - 1)) :=
            ((continuous_const.sub continuous_id).tendsto (1 : ℝ)).mono_left
              nhdsWithin_le_nhds
          simpa using h
        · filter_upwards [self_mem_nhdsWithin] with w hw
          exact sub_pos.mpr hw
      have hcont : Tendsto li2PowerSeries (𝓝[>] (0 : ℝ)) (𝓝 (li2PowerSeries 0)) :=
        continuousAt_li2PowerSeries_zero.tendsto.mono_left nhdsWithin_le_nhds
      rw [li2PowerSeries_zero] at hcont
      exact hcont.comp hmap
    have hprod : Tendsto (fun w => log w * log (1 - w)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have key : Tendsto (fun w => (log w / (1 - w)) * ((1 - w) * log (1 - w)))
          (𝓝[<] (1 : ℝ)) (𝓝 ((-1) * 0)) :=
        tendsto_log_div_one_sub_nhdsLT_one.mul
          tendsto_one_sub_mul_log_one_sub_nhdsLT_one
      rw [mul_zero] at key
      refine key.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have h1w : (1 : ℝ) - w ≠ 0 := (sub_pos.mpr hw).ne'
      field_simp
    have hsumT := (tendsto_li2PowerSeries_nhdsLT_one.add hcomp).add hprod
    simpa using hsumT
  have hlimC : Tendsto (fun w => li2PowerSeries w + li2PowerSeries (1 - w) + log w * log (1 - w))
      (𝓝[<] (1 : ℝ))
      (𝓝 (li2PowerSeries (1 / 2) + li2PowerSeries (1 - 1 / 2) +
        log (1 / 2) * log (1 - 1 / 2))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds zero_lt_one)]
      with w hw1 hw0
    exact (hconst w ⟨hw0, hw1⟩).symm
  have hval := tendsto_nhds_unique hlimC hlim
  have hSz := hconst z hz
  linarith [hSz, hval]

end Real
