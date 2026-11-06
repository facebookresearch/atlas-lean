/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Power-growth exceptional sets

This file proves that the points where a positive monotone smooth real function grows at
least as fast as a fixed power greater than one form a set of finite Lebesgue measure.
-/

@[expose] public section

namespace Real

open Filter MeasureTheory Set
open scoped ENNReal Interval

/-- **Power-growth exceptional set.** For a function $h : \mathbb{R} \to \mathbb{R}$ and real
numbers $p$ and $x_0$, this is the set of real numbers $x \ge x_0$ such that
$h(x)^p \le h'(x)$, where $h(x)^p$ is the real power and $h'(x)$ is the derivative of $h$ at
$x$, taken to be $0$ where $h$ is not differentiable. -/
def powerGrowthBadSet (h : ℝ → ℝ) (p x₀ : ℝ) : Set ℝ :=
  {x | x₀ ≤ x ∧ h x ^ p ≤ deriv h x}

/-- **The power-growth exceptional set has finite measure.** Let $p > 1$ and $x_0$ be real
numbers, and let $h : \mathbb{R} \to \mathbb{R}$ be continuously differentiable, with
$h(x) > 0$ for all $x \ge x_0$ and $h$ nondecreasing on $[x_0, \infty)$. Then the
power-growth exceptional set of $h$, the set of $x \ge x_0$ with $h(x)^p \le h'(x)$, has finite
Lebesgue measure. -/
theorem volume_powerGrowthBadSet_lt_top
    (h : ℝ → ℝ) {p x₀ : ℝ} (hp : 1 < p)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x)
    (hmono : MonotoneOn h (Ici x₀))
    (hsmooth : ContDiff ℝ 1 h) :
    volume (powerGrowthBadSet h p x₀) < ∞ := by
  let q : ℝ → ℝ := fun x ↦ deriv h x / h x ^ p
  let H : ℝ → ℝ := fun x ↦ h x ^ (1 - p) / (1 - p)
  let C : ℝ := -H x₀
  have hdiff : Differentiable ℝ h := hsmooth.differentiable (by norm_num)
  have hderiv_cont : Continuous (deriv h) := hsmooth.continuous_deriv (by norm_num)
  have hderiv_nonneg {x : ℝ} (hx : x₀ < x) : 0 ≤ deriv h x := by
    have hnhds : Ici x₀ ∈ nhds x :=
      mem_of_superset (Ioi_mem_nhds hx) Ioi_subset_Ici_self
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hmono.derivWithin_nonneg
  have hq_continuousOn {b : ℝ} (hxb : x₀ ≤ b) :
      ContinuousOn q (Icc x₀ b) := by
    have hhpow : ContinuousOn (fun x ↦ h x ^ p) (Icc x₀ b) :=
      hsmooth.continuous.continuousOn.rpow_const fun x hx ↦
        Or.inl (hpos x hx.1).ne'
    exact hderiv_cont.continuousOn.div hhpow fun x hx ↦
      (Real.rpow_pos_of_pos (hpos x hx.1) p).ne'
  have hH_deriv {b : ℝ} (hxb : x₀ ≤ b) :
      ∀ x ∈ Icc x₀ b, HasDerivAt H (q x) x := by
    intro x hx
    have hhx : 0 < h x := hpos x hx.1
    have hpne : 1 - p ≠ 0 := by linarith
    have hbase := ((hdiff x).hasDerivAt.rpow_const (p := 1 - p) (Or.inl hhx.ne')).div_const
      (1 - p)
    have hcoeff :
        deriv h x * (1 - p) * h x ^ (1 - p - 1) / (1 - p) =
          deriv h x / h x ^ p := by
      have hrpow_ne : h x ^ p ≠ 0 := (Real.rpow_pos_of_pos hhx p).ne'
      rw [show 1 - p - 1 = -p by ring, Real.rpow_neg hhx.le]
      field_simp [hpne, hrpow_ne]
    rw [hcoeff] at hbase
    simpa only [H, q] using hbase
  have hfinite_section (b : ℝ) :
      volume (powerGrowthBadSet h p x₀ ∩ Icc x₀ b) ≤ ENNReal.ofReal C := by
    by_cases hxb : x₀ ≤ b
    · have hqint : IntervalIntegrable q volume x₀ b :=
        (hq_continuousOn hxb).intervalIntegrable_of_Icc hxb
      have hqint_Ioc : IntegrableOn q (Ioc x₀ b) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hxb).mp hqint
      have hindicator : Integrable ((Ioc x₀ b).indicator q) volume :=
        hqint_Ioc.integrable_indicator measurableSet_Ioc
      have hindicator_nonneg :
          0 ≤ᵐ[volume] (Ioc x₀ b).indicator q := by
        filter_upwards with x
        by_cases hx : x ∈ Ioc x₀ b
        · rw [indicator_of_mem hx]
          exact div_nonneg (hderiv_nonneg hx.1)
            (Real.rpow_nonneg (hpos x hx.1.le).le p)
        · simp [Set.indicator_of_notMem hx]
      have hone_le (x : ℝ)
          (hx : x ∈ powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) :
          1 ≤ (Ioc x₀ b).indicator q x := by
        rw [indicator_of_mem hx.2]
        change 1 ≤ deriv h x / h x ^ p
        exact (le_div_iff₀ (Real.rpow_pos_of_pos (hpos x hx.1.1) p)).2 (by
          simpa using hx.1.2)
      have hmeasure_Ioc :
          volume (powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) ≤
            ENNReal.ofReal (∫ x, (Ioc x₀ b).indicator q x) :=
        hindicator.measure_le_integral hindicator_nonneg hone_le
      have hH_deriv_uIcc :
          ∀ x ∈ uIcc x₀ b, HasDerivAt H (q x) x := by
        simpa only [uIcc_of_le hxb] using hH_deriv hxb
      have hFTC : ∫ x in x₀..b, q x = H b - H x₀ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hH_deriv_uIcc hqint
      have hintegral_le : ∫ x in x₀..b, q x ≤ C := by
        rw [hFTC]
        change H b - H x₀ ≤ -H x₀
        have hdenom : 1 - p < 0 := sub_neg.mpr hp
        have hHb : H b ≤ 0 := by
          change h b ^ (1 - p) / (1 - p) ≤ 0
          exact div_nonpos_of_nonneg_of_nonpos
            (Real.rpow_nonneg (hpos b hxb).le (1 - p)) hdenom.le
        linarith
      have hmeasure_Icc :
          volume (powerGrowthBadSet h p x₀ ∩ Icc x₀ b) ≤
            volume (powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) := by
        calc
          volume (powerGrowthBadSet h p x₀ ∩ Icc x₀ b) ≤
              volume ((powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) ∪ {x₀}) :=
            measure_mono fun x hx ↦ by
              by_cases hxx₀ : x = x₀
              · exact Or.inr hxx₀
              · exact Or.inl ⟨hx.1, lt_of_le_of_ne hx.2.1 (Ne.symm hxx₀), hx.2.2⟩
          _ ≤ volume (powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) + volume ({x₀} : Set ℝ) :=
            measure_union_le _ _
          _ = volume (powerGrowthBadSet h p x₀ ∩ Ioc x₀ b) := by simp
      refine hmeasure_Icc.trans (hmeasure_Ioc.trans ?_)
      rw [integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hxb]
      exact ENNReal.ofReal_le_ofReal hintegral_le
    · have hempty : Icc x₀ b = ∅ := Icc_eq_empty hxb
      simp [hempty]
  have hsections_mono :
      Monotone (fun b : ℝ ↦ powerGrowthBadSet h p x₀ ∩ Icc x₀ b) := by
    intro a b hab x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans hab⟩
  have hsections_union :
      (⋃ b : ℝ, powerGrowthBadSet h p x₀ ∩ Icc x₀ b) =
        powerGrowthBadSet h p x₀ := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨b, hx⟩
      exact hx.1
    · intro hx
      rw [Set.mem_iUnion]
      exact ⟨x, ⟨hx, hx.1, le_rfl⟩⟩
  rw [← hsections_union, hsections_mono.measure_iUnion]
  exact lt_of_le_of_lt (iSup_le hfinite_section) (by simp)

end Real
