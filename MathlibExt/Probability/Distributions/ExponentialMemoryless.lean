/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The memoryless characterization of the exponential law -/

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

private theorem survival_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Ioi t) = 1 - cdf μ t := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]

private theorem cdf_eq_zero_of_lt_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {x : ℝ} (hx : x < 0) : cdf μ x = 0 := by
  rw [cdf_eq_real, measureReal_eq_zero_iff]
  exact measure_mono_null (fun _ hy => hy.trans_lt hx) hμ

/-- An additive monotone function on the nonnegative half-line is determined by its value at 1.
The floor of `n * x` bounds the value at `n * x` between two consecutive integer values. -/
private theorem eq_mul_of_monotoneOn_of_add (f : ℝ → ℝ) (h0 : f 0 = 0)
    (hmono : MonotoneOn f (Ici 0))
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    {x : ℝ} (hx : 0 ≤ x) : f x = f 1 * x := by
  have hnat (y : ℝ) (hy : 0 ≤ y) (n : ℕ) : f (n * y) = n * f y := by
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ (by positivity) hy, ih]
      ring
  have hr : 0 ≤ f 1 := h0 ▸ hmono (by simp) (by norm_num) (by norm_num)
  have hbound (n : ℕ) : |(n : ℝ) * (f x - f 1 * x)| ≤ f 1 := by
    let m : ℕ := ⌊(n : ℝ) * x⌋₊
    have hlo : (m : ℝ) ≤ (n : ℝ) * x := Nat.floor_le (by positivity)
    have hhi : (n : ℝ) * x ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    have hflo := hmono (show (m : ℝ) ∈ Ici 0 from Nat.cast_nonneg m)
      (show (n : ℝ) * x ∈ Ici 0 from mul_nonneg (Nat.cast_nonneg n) hx) hlo
    have hfhi := hmono (show (n : ℝ) * x ∈ Ici 0 from mul_nonneg (Nat.cast_nonneg n) hx)
      (show (m : ℝ) + 1 ∈ Ici 0 from add_nonneg (Nat.cast_nonneg m) zero_le_one) hhi
    have hcast (j : ℕ) : f j = j * f 1 := by simpa using hnat 1 zero_le_one j
    rw [hcast, hnat x hx] at hflo
    rw [hnat x hx, hadd _ _ (Nat.cast_nonneg _) zero_le_one, hcast] at hfhi
    rw [abs_le]
    constructor
    · nlinarith only [hflo, mul_le_mul_of_nonneg_right hhi hr]
    · nlinarith only [hfhi, mul_le_mul_of_nonneg_right hlo hr]
  by_contra h
  have hd : 0 < |f x - f 1 * x| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨n, hn⟩ := exists_nat_gt (f 1 / |f x - f 1 * x|)
  have hb := hbound n
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hb
  exact (not_lt_of_ge hb) ((div_lt_iff₀ hd).mp hn)

private theorem survival_eq_exp_of_memoryless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hzero : μ.real (Ioi 0) = 1)
    (hm : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      μ.real (Ioi (s + t)) = μ.real (Ioi s) * μ.real (Ioi t)) :
    ∃ r > 0, ∀ t : ℝ, 0 ≤ t → μ.real (Ioi t) = Real.exp (-(r * t)) := by
  let S (t : ℝ) := μ.real (Ioi t)
  have hS (t : ℝ) : S t = 1 - cdf μ t := survival_eq_one_sub_cdf μ t
  have hcont : ContinuousWithinAt S (Ici 0) 0 := by
    rw [show S = fun t : ℝ => 1 - cdf μ t from funext hS]
    exact continuousWithinAt_const.sub ((cdf μ).right_continuous 0)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp hcont (1 / 2) (by norm_num)
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < S t := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / δ)
    have hn' : (0 : ℝ) < n := (div_nonneg ht hδ.le).trans_lt hn
    let u := t / (n : ℝ)
    have hu : 0 ≤ u := div_nonneg ht hn'.le
    have huδ : u < δ := by
      exact (div_lt_iff₀ hn').mpr (by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn)
    have hclose := hnear (show u ∈ Ici 0 from hu)
      (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hu])
    have hu' : 0 < S u := by
      rw [Real.dist_eq, show S 0 = 1 from hzero] at hclose
      linarith [neg_abs_le (S u - 1)]
    have hnS (j : ℕ) : S (j * u) = (S u) ^ j := by
      induction j with
      | zero => simpa using hzero
      | succ j ih =>
        have hs : S ((j : ℝ) * u + u) = S ((j : ℝ) * u) * S u :=
          hm _ _ (mul_nonneg (Nat.cast_nonneg j) hu) hu
        rw [Nat.cast_succ, add_mul, one_mul, hs, ih, pow_succ]
    rw [← div_mul_cancel₀ t hn'.ne', mul_comm (t / (n : ℝ)) (n : ℝ)]
    exact (hnS n).symm ▸ pow_pos hu' n
  let f (t : ℝ) := -Real.log (S t)
  have hf0 : f 0 = 0 := by simp [f, show S 0 = 1 from hzero]
  have hfmono : MonotoneOn f (Ici 0) := by
    intro x hx y _ hxy
    exact neg_le_neg (Real.log_le_log (hpos y (hx.trans hxy))
      (measureReal_mono fun _ hz => hxy.trans_lt hz))
  have hfadd (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : f (x + y) = f x + f y := by
    dsimp only [f]
    rw [show S (x + y) = S x * S y from hm x y hx hy,
      Real.log_mul (hpos x hx).ne' (hpos y hy).ne', neg_add]
  have hexp (t : ℝ) (ht : 0 ≤ t) : S t = Real.exp (-(f 1 * t)) := by
    rw [← eq_mul_of_monotoneOn_of_add f hf0 hfmono hfadd ht]
    simp [f, Real.exp_log (hpos t ht)]
  have hr0 : 0 ≤ f 1 := hf0 ▸ hfmono (by simp) (by norm_num) (by norm_num)
  have hr : 0 < f 1 := by
    by_contra h
    have hrate : f 1 = 0 := le_antisymm (le_of_not_gt h) hr0
    have hvanish : ∀ᶠ t : ℝ in atTop, (cdf μ t : ℝ) = 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have h := hexp t ht
      rw [hS, hrate, zero_mul, neg_zero, Real.exp_zero] at h
      linarith
    have hlim : Tendsto (fun t : ℝ => (cdf μ t : ℝ)) atTop (𝓝 0) :=
      (tendsto_congr' hvanish).mpr tendsto_const_nhds
    exact zero_ne_one (tendsto_nhds_unique hlim (tendsto_cdf_atTop μ))
  exact ⟨f 1, hr, hexp⟩

/-- **The memoryless property characterizes the exponential law.** A probability law on the
nonnegative reals has multiplicative survival probabilities at all nonnegative times if and only
if it is the point mass at zero or an exponential law of positive rate. The point mass is included
because the statement uses the unconditional product identity even when survival is zero.
Adan and Resing, *Queueing Systems*, §2.4.3, give the exponential law's memoryless property;
the converse follows by taking logarithms on the positive branch. -/
public theorem memoryless_iff_dirac_zero_or_expMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      μ.real (Ioi (s + t)) = μ.real (Ioi s) * μ.real (Ioi t)) ↔
      μ = Measure.dirac 0 ∨ ∃ r > 0, μ = expMeasure r := by
  constructor
  · intro hm
    have h := hm 0 0 le_rfl le_rfl
    rw [zero_add] at h
    have hfactor : μ.real (Ioi 0) * (μ.real (Ioi 0) - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with hz | hz
    · left
      apply Measure.eq_of_cdf
      apply StieltjesFunction.ext
      intro t
      rw [cdf_eq_real (Measure.dirac 0)]
      by_cases ht : 0 ≤ t
      · have htail : μ.real (Ioi t) = 0 :=
          measureReal_mono_null (fun _ ht' => ht.trans_lt ht') hz
        rw [survival_eq_one_sub_cdf] at htail
        have hc : cdf μ t = 1 := by linarith
        simp [hc, Measure.real, Measure.dirac_apply' _ measurableSet_Iic, ht]
      · rw [cdf_eq_zero_of_lt_zero μ hμ (lt_of_not_ge ht)]
        simp [Measure.real, Measure.dirac_apply' _ measurableSet_Iic, ht]
    · right
      obtain ⟨r, hr, htail⟩ := survival_eq_exp_of_memoryless μ (sub_eq_zero.mp hz) hm
      let _ := isProbabilityMeasure_expMeasure hr
      refine ⟨r, hr, Measure.eq_of_cdf μ _ (StieltjesFunction.ext fun t => ?_)⟩
      rw [cdf_expMeasure_eq hr]
      by_cases ht : 0 ≤ t
      · rw [ite_eq_left ht]
        have h := htail t ht
        rw [survival_eq_one_sub_cdf] at h
        linarith
      · simp [ht, cdf_eq_zero_of_lt_zero μ hμ (lt_of_not_ge ht)]
  · rintro (rfl | ⟨r, hr, rfl⟩) s t hs ht
    · simp [Measure.real, Measure.dirac_apply' _ measurableSet_Ioi,
        not_lt_of_ge hs, not_lt_of_ge ht, not_lt_of_ge (add_nonneg hs ht)]
    · let _ := isProbabilityMeasure_expMeasure hr
      simp only [survival_eq_one_sub_cdf, cdf_expMeasure_eq hr, ite_eq_left hs, ite_eq_left ht,
        ite_eq_left (add_nonneg hs ht), sub_sub_cancel]
      rw [mul_add, neg_add, Real.exp_add]

end ProbabilityTheory
