/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Paleoclimate proxies and orbital forcing

## i. Overview

For a stipulated elliptic orbit with `0 ≤ e < 1`, `a > 0`, `r θ = a(1 - e²)/(1 + e cos θ)`, and
  areal-law time weighting `dt ∝ r² dθ`, the annual average of `1 / r²` is `1 / (a²√(1 - e²))`. The
  ellipse area integral `∫₀^{2π} r² = 2πa²√(1 - e²)` is an explicit hypothesis, not proved here;
  this is conditional orbital geometry, not proxy causation and not a full two-body derivation.

## ii. Key results

- `EarthScience.orbital_time_average_inv_r_sq`: the time-weighted average of `1 / r²`.

## iii. Table of contents

- A. Orbital average

## iv. References

- `intervalIntegral.integral_congr_ae`, `intervalIntegral.integral_const`,
  `intervalIntegral.integral_div` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Annual average of `1 / r²` for a stipulated elliptic orbit. With
`0 ≤ e < 1`, `a > 0`, `r θ = a * (1 - e²) / (1 + e * cos θ)`, areal-law
time weighting `dt ∝ r² dθ` with areal constant `h > 0`, and the stipulated
area integral `∫ θ in 0..2π, (r θ)² = 2π * a² * √(1 - e²)` (the ellipse
area integral, taken as a hypothesis, not proved here), the time-weighted
average of `1 / r²` over one period is `1 / (a² * √(1 - e²))`. -/
theorem orbital_time_average_inv_r_sq {a e h : ℝ} (ha : 0 < a)
    (he0 : 0 ≤ e) (he1 : e < 1) (hh : 0 < h)
    (r : ℝ → ℝ) (hr : ∀ θ, r θ = a * (1 - e ^ 2) / (1 + e * Real.cos θ))
    (hArea : ∫ θ in (0)..(2 * Real.pi), (r θ) ^ 2 =
      2 * Real.pi * a ^ 2 * Real.sqrt (1 - e ^ 2)) :
    (∫ θ in (0)..(2 * Real.pi), (1 / (r θ) ^ 2) * ((r θ) ^ 2 / h)) /
      (∫ θ in (0)..(2 * Real.pi), (r θ) ^ 2 / h) =
      1 / (a ^ 2 * Real.sqrt (1 - e ^ 2)) := by
  have he_sq_lt : e ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 - e := by linarith
    have h2 : (0 : ℝ) < 1 + e := by linarith
    have h3 : (0 : ℝ) < (1 - e) * (1 + e) := mul_pos h1 h2
    have hring : (1 - e) * (1 + e) = 1 - e ^ 2 := by ring
    linarith
  have h1e2 : (0 : ℝ) < 1 - e ^ 2 := by linarith
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (1 - e ^ 2) := Real.sqrt_pos_of_pos h1e2
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt h2pi_pos
  have hdenom_pos : ∀ θ, (0 : ℝ) < 1 + e * Real.cos θ := by
    intro θ
    have hcos : (-1 : ℝ) ≤ Real.cos θ := Real.neg_one_le_cos θ
    have hmul : e * (-1) ≤ e * Real.cos θ := mul_le_mul_of_nonneg_left hcos he0
    have hle : (-e : ℝ) ≤ e * Real.cos θ := by linarith
    have h1e : (0 : ℝ) < 1 - e := by linarith
    linarith
  have hr_pos : ∀ θ, (0 : ℝ) < r θ := by
    intro θ
    rw [hr θ]
    exact div_pos (mul_pos ha h1e2) (hdenom_pos θ)
  have hr_ne : ∀ θ, r θ ≠ 0 := fun θ => ne_of_gt (hr_pos θ)
  have hsq_ne : ∀ θ, (r θ) ^ 2 ≠ 0 := fun θ => pow_ne_zero 2 (hr_ne θ)
  have hnum_eq : ∀ θ, (1 / (r θ) ^ 2) * ((r θ) ^ 2 / h) = 1 / h := by
    intro θ
    have hy : (r θ) ^ 2 ≠ 0 := hsq_ne θ
    have hr0 : r θ ≠ 0 := hr_ne θ
    field_simp
  have hnum_int : (∫ θ in (0)..(2 * Real.pi), (1 / (r θ) ^ 2) * ((r θ) ^ 2 / h)) =
      ∫ θ in (0)..(2 * Real.pi), (1 / h : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ _ => hnum_eq θ)
  have hconst : (∫ θ in (0)..(2 * Real.pi), (1 / h : ℝ)) = 2 * Real.pi / h := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div]
  have hdenom : (∫ θ in (0)..(2 * Real.pi), (r θ) ^ 2 / h) =
      (∫ θ in (0)..(2 * Real.pi), (r θ) ^ 2) / h := by
    exact intervalIntegral.integral_div h (fun θ => (r θ) ^ 2)
  rw [hnum_int, hconst, hdenom, hArea]
  have ha2_pos : (0 : ℝ) < a ^ 2 := by positivity
  have ha2_ne : a ^ 2 ≠ 0 := ne_of_gt ha2_pos
  have hsqrt_ne : Real.sqrt (1 - e ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hprod_ne : a ^ 2 * Real.sqrt (1 - e ^ 2) ≠ 0 := mul_ne_zero ha2_ne hsqrt_ne
  have hbig_pos : (0 : ℝ) < 2 * Real.pi * a ^ 2 * Real.sqrt (1 - e ^ 2) := by positivity
  have hbig_ne : 2 * Real.pi * a ^ 2 * Real.sqrt (1 - e ^ 2) ≠ 0 := ne_of_gt hbig_pos
  field_simp

end EarthScience
