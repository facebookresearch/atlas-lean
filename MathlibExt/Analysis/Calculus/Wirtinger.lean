/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Wirtinger's inequality

This file proves the endpoint-zero form of Wirtinger's integral inequality on `[0, π]` using a
smooth Riccati comparison function, together with the scaled derivative-field form on a
general interval `[a, b]`.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem wirtinger_angle_mem_Ioo {c x : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    c * (x - Real.pi / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpi_half : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hl : -(Real.pi / 2) ≤ x - Real.pi / 2 := by linarith [hx.1]
  have hu : x - Real.pi / 2 ≤ Real.pi / 2 := by linarith [hx.2]
  have hmul_lower := mul_le_mul_of_nonneg_left hl hc_pos.le
  have hmul_upper := mul_le_mul_of_nonneg_left hu hc_pos.le
  constructor <;> nlinarith

private theorem wirtinger_weight_hasDerivWithinAt {c x : ℝ} (hc_pos : 0 < c)
    (hc_lt_one : c < 1) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    HasDerivWithinAt (fun y : ℝ => -c * Real.tan (c * (y - Real.pi / 2)))
      (-(c ^ 2) / Real.cos (c * (x - Real.pi / 2)) ^ 2) (Set.Icc 0 Real.pi) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * (y - Real.pi / 2)) c x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).sub_const (Real.pi / 2)).const_mul c
  have htan :=
    (Real.hasDerivAt_tan_of_mem_Ioo (wirtinger_angle_mem_Ioo hc_pos hc_lt_one hx)).comp
      x hinner
  convert (htan.const_mul (-c)).hasDerivWithinAt using 1
  · simp only [Function.comp_apply]
  · ring

private theorem wirtinger_riccati_identity {c x : ℝ} (hc_pos : 0 < c)
    (hc_lt_one : c < 1) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    -(c ^ 2) / Real.cos (c * (x - Real.pi / 2)) ^ 2 +
        (-c * Real.tan (c * (x - Real.pi / 2))) ^ 2 =
      -(c ^ 2) := by
  let t := c * (x - Real.pi / 2)
  change -(c ^ 2) / Real.cos t ^ 2 + (-c * Real.tan t) ^ 2 = -(c ^ 2)
  have hcos : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (wirtinger_angle_mem_Ioo hc_pos hc_lt_one hx)).ne'
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem wirtinger_product_hasDerivWithinAt {f f' : ℝ → ℝ} {c x : ℝ}
    (hf_deriv : ∀ y ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt f (f' y) (Set.Icc 0 Real.pi) y)
    (hc_pos : 0 < c) (hc_lt_one : c < 1) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    HasDerivWithinAt
      (fun y : ℝ => (-c * Real.tan (c * (y - Real.pi / 2))) * f y ^ 2)
      (-(c ^ 2) / Real.cos (c * (x - Real.pi / 2)) ^ 2 * f x ^ 2 +
        (-c * Real.tan (c * (x - Real.pi / 2))) * (2 * f x * f' x))
      (Set.Icc 0 Real.pi) x := by
  convert (wirtinger_weight_hasDerivWithinAt hc_pos hc_lt_one hx).mul
    ((hf_deriv x hx).pow 2) using 1
  norm_num [Pi.pow_apply]

private theorem wirtinger_pointwise_bound {f f' : ℝ → ℝ} {c x : ℝ} :
    (f' x ^ 2 - (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x) ^ 2 -
          c ^ 2 * f x ^ 2) +
        c ^ 2 * f x ^ 2 ≤
      f' x ^ 2 := by
  nlinarith [sq_nonneg (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x)]

private theorem wirtinger_product_hasDerivWithinAt_algebraic {f f' : ℝ → ℝ} {c x : ℝ}
    (hf_deriv : ∀ y ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt f (f' y) (Set.Icc 0 Real.pi) y)
    (hc_pos : 0 < c) (hc_lt_one : c < 1) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
    HasDerivWithinAt
      (fun y : ℝ => (-c * Real.tan (c * (y - Real.pi / 2))) * f y ^ 2)
      (f' x ^ 2 -
        (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x) ^ 2 -
        c ^ 2 * f x ^ 2)
      (Set.Icc 0 Real.pi) x := by
  convert wirtinger_product_hasDerivWithinAt hf_deriv hc_pos hc_lt_one hx using 1
  have hriccati := wirtinger_riccati_identity hc_pos hc_lt_one hx
  have hderiv :
      -(c ^ 2) / Real.cos (c * (x - Real.pi / 2)) ^ 2 =
        -(c ^ 2) - (-c * Real.tan (c * (x - Real.pi / 2))) ^ 2 := by
    linarith
  rw [hderiv]
  ring

private theorem wirtinger_scaled_integral_le (f f' : ℝ → ℝ)
    (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt f (f' x) (Set.Icc 0 Real.pi) x)
    (hf_deriv_cont : ContinuousOn f' (Set.Icc 0 Real.pi))
    (h0 : f 0 = 0) (hpi : f Real.pi = 0) {c : ℝ}
    (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    c ^ 2 * intervalIntegral (fun x => f x ^ 2) 0 Real.pi MeasureTheory.volume ≤
      intervalIntegral (fun x => f' x ^ 2) 0 Real.pi MeasureTheory.volume := by
  have hpi_nonneg : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) Real.pi) :=
    fun x hx => (hf_deriv x hx).continuousWithinAt
  have hweight_cont : ContinuousOn
      (fun x : ℝ => -c * Real.tan (c * (x - Real.pi / 2)))
      (Set.Icc 0 Real.pi) :=
    fun x hx => (wirtinger_weight_hasDerivWithinAt hc_pos hc_lt_one hx).continuousWithinAt
  have hderivand_cont : ContinuousOn
      (fun x : ℝ =>
        f' x ^ 2 -
          (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x) ^ 2 -
          c ^ 2 * f x ^ 2)
      (Set.Icc 0 Real.pi) := by
    fun_prop
  have hscaled_cont : ContinuousOn (fun x : ℝ => c ^ 2 * f x ^ 2)
      (Set.Icc 0 Real.pi) := by
    simpa only [Pi.pow_apply] using (hf_cont.pow 2).const_mul (c ^ 2)
  have hright_cont : ContinuousOn (fun x : ℝ => f' x ^ 2) (Set.Icc 0 Real.pi) := by
    fun_prop
  have hderivand_int := hderivand_cont.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hpi_nonneg
  have hscaled_int := hscaled_cont.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hpi_nonneg
  have hright_int := hright_cont.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hpi_nonneg
  have hmono := intervalIntegral.integral_mono_on hpi_nonneg
    ((hderivand_cont.add hscaled_cont).intervalIntegrable_of_Icc hpi_nonneg)
    hright_int (fun x _ => wirtinger_pointwise_bound)
  have hproduct_cont : ContinuousOn
      (fun x : ℝ => (-c * Real.tan (c * (x - Real.pi / 2))) * f x ^ 2)
      (Set.Icc 0 Real.pi) := by
    fun_prop
  have hproduct_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt
        (fun y : ℝ => (-c * Real.tan (c * (y - Real.pi / 2))) * f y ^ 2)
        (f' x ^ 2 -
          (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x) ^ 2 -
          c ^ 2 * f x ^ 2) x := by
    intro x hx
    exact (wirtinger_product_hasDerivWithinAt_algebraic hf_deriv hc_pos hc_lt_one
      ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpi_nonneg
    hproduct_cont hproduct_deriv hderivand_int
  have hderivand_zero : intervalIntegral
      (fun x : ℝ =>
        f' x ^ 2 -
          (f' x - (-c * Real.tan (c * (x - Real.pi / 2))) * f x) ^ 2 -
          c ^ 2 * f x ^ 2)
      0 Real.pi MeasureTheory.volume = 0 := by
    rw [hFTC]
    simp [h0, hpi]
  simp only [Pi.add_apply] at hmono
  rw [intervalIntegral.integral_add hderivand_int hscaled_int,
    intervalIntegral.integral_const_mul, hderivand_zero, zero_add] at hmono
  exact hmono

private theorem wirtinger_limit {A B : ℝ}
    (hscaled : ∀ c : ℝ, 0 < c → c < 1 → c ^ 2 * A ≤ B) : A ≤ B := by
  by_contra hle
  have hBA : B < A := lt_of_not_ge hle
  have hhalf := hscaled (1 / 2) (by norm_num) (by norm_num)
  norm_num at hhalf
  have hB : 0 ≤ B := by nlinarith [hhalf, hBA]
  have hA_pos : 0 < A := lt_of_le_of_lt hB hBA
  let c := (A + B) / (2 * A)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by positivity)
  have hc_lt_one : c < 1 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hgap : 0 < (A - B) * (A - B) :=
    mul_pos (sub_pos.mpr hBA) (sub_pos.mpr hBA)
  have hstrict : B < c ^ 2 * A := by
    calc
      B < (A + B) ^ 2 / (4 * A) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith
      _ = c ^ 2 * A := by
        dsimp [c]
        field_simp [ne_of_gt hA_pos]
        ring
  exact (not_lt_of_ge (hscaled c hc_pos hc_lt_one)) hstrict

/-- **Wirtinger's inequality.** Let $f, f' : \mathbb{R} \to \mathbb{R}$ be functions such that
for every $x \in [0, \pi]$ the function $f$ has derivative $f'(x)$ at $x$ within $[0, \pi]$, $f'$
is continuous on $[0, \pi]$, and $f(0) = f(\pi) = 0$. Then
$\int_0^\pi f(x)^2 \, dx \le \int_0^\pi f'(x)^2 \, dx$.

Proof: A Picone-type comparison. For `0 < c < 1` the weight `h x = -c * tan (c * (x - π / 2))` is
smooth on `[0, π]` with `h' + h ^ 2 = -c ^ 2`, so integrating
`f' ^ 2 = (f' - h * f) ^ 2 + (h * f ^ 2)' + c ^ 2 * f ^ 2` gives `c ^ 2 * ∫ f ^ 2 ≤ ∫ f' ^ 2`;
then let `c` tend to one.

Proves `Wanted` entry `wirtinger_inequality`.

Source: G. H. Hardy, J. E. Littlewood, and G. Pólya, *Inequalities*, second edition,
Cambridge University Press, 1952, §7.7 (the endpoint-zero form on `[0, L]`).
-/
public theorem wirtinger_inequality (f f' : ℝ → ℝ)
    (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt f (f' x) (Set.Icc 0 Real.pi) x)
    (hf_deriv_cont : ContinuousOn f' (Set.Icc 0 Real.pi))
    (h0 : f 0 = 0) (hpi : f Real.pi = 0) :
    intervalIntegral (fun x => (f x) ^ 2) 0 Real.pi MeasureTheory.volume ≤
      intervalIntegral (fun x => (f' x) ^ 2) 0 Real.pi MeasureTheory.volume := by
  apply wirtinger_limit
  intro c hc_pos hc_lt_one
  exact wirtinger_scaled_integral_le f f' hf_deriv hf_deriv_cont h0 hpi hc_pos hc_lt_one

/-- Wirtinger's inequality on a general interval `[a, b]` with `a < b`, in
derivative-field form: a function `f` with derivative field `f'` within `[a, b]`,
`f'` continuous on `[a, b]`, vanishing at the endpoints, satisfies
`∫ₐᵇ f² ≤ ((b - a) / π)² ∫ₐᵇ (f')²`.

Proof: rescale `[a, b]` to `[0, π]` and apply `wirtinger_inequality`. -/
public theorem wirtinger_inequality_Icc {a b : ℝ} (hab : a < b) (f f' : ℝ → ℝ)
    (hf_deriv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (f' x) (Set.Icc a b) x)
    (hf_deriv_cont : ContinuousOn f' (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    intervalIntegral (fun x => (f x) ^ 2) a b MeasureTheory.volume ≤
      ((b - a) / Real.pi) ^ 2 *
        intervalIntegral (fun x => (f' x) ^ 2) a b MeasureTheory.volume := by
  set s := (b - a) / Real.pi with hs
  have hs0 : 0 < s := div_pos (sub_pos.mpr hab) Real.pi_pos
  have hend : a + s * Real.pi = b := by
    rw [hs, div_mul_cancel₀ _ Real.pi_pos.ne']
    ring
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, a + s * t ∈ Set.Icc a b := by
    intro t ht
    constructor
    · have hnonneg : 0 ≤ s * t := mul_nonneg hs0.le ht.1
      linarith
    · have hle : s * t ≤ s * Real.pi := mul_le_mul_of_nonneg_left ht.2 hs0.le
      linarith [hend]
  have hF : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt (fun t => f (a + s * t)) (f' (a + s * t) * s)
        (Set.Icc 0 Real.pi) t := by
    intro t ht
    have h1a : HasDerivAt (fun t : ℝ => a + s * t) s t := by
      simpa using ((hasDerivAt_id t).const_mul s).const_add a
    have h1 : HasDerivWithinAt (fun t : ℝ => a + s * t) s (Set.Icc 0 Real.pi) t :=
      h1a.hasDerivWithinAt
    exact (hf_deriv _ (hmem t ht)).comp t h1 (fun u hu => hmem u hu)
  have hlin : Continuous fun t : ℝ => a + s * t := by fun_prop
  have hcomp : ContinuousOn (fun t => f' (a + s * t)) (Set.Icc 0 Real.pi) :=
    hf_deriv_cont.comp' hlin.continuousOn (fun t ht => hmem t ht)
  have hw := wirtinger_inequality (fun t => f (a + s * t))
    (fun t => f' (a + s * t) * s) (fun t ht => hF t ht)
    (hcomp.mul_const s) (by simp [ha]) (by simp [hend, hb])
  have h1 : ∫ t in (0 : ℝ)..Real.pi, f (a + s * t) ^ 2 =
      s⁻¹ * ∫ x in a..b, f x ^ 2 := by
    have := intervalIntegral.integral_comp_add_mul (fun x => f x ^ 2) (a := 0)
      (b := Real.pi) hs0.ne' a
    simpa [hend] using this
  have h2 : ∫ t in (0 : ℝ)..Real.pi, (f' (a + s * t) * s) ^ 2 =
      s ^ 2 * (s⁻¹ * ∫ x in a..b, f' x ^ 2) := by
    have := intervalIntegral.integral_comp_add_mul (fun x => f' x ^ 2) (a := 0)
      (b := Real.pi) hs0.ne' a
    simp only [mul_zero, add_zero, hend, smul_eq_mul] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [h1, h2] at hw
  have hmul := mul_le_mul_of_nonneg_left hw hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at hmul
  calc ∫ x in a..b, f x ^ 2 ≤ s * (s ^ 2 * (s⁻¹ * ∫ x in a..b, f' x ^ 2)) := hmul
    _ = s ^ 2 * ∫ x in a..b, f' x ^ 2 := by
        field_simp

end MetaMathlibExt
