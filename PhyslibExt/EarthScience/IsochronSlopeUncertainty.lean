
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Isochron slope-uncertainty propagation with an explicit remainder

For decay constant `λ > 0`, slope `m > 0` and nonnegative slope
perturbation `δ ≥ 0`, the age change differs from the first-order
derivative term `δ / (λ * (1 + m))` by at most the explicit remainder
`δ ^ 2 / (2 * λ * (1 + m) ^ 2)`.

## i. Overview

Write the age as `log (1 + m) / λ` and set `u = δ / (1 + m) ≥ 0`. Then
`log (1 + (m + δ)) - log (1 + m) = log (1 + u)`, and the claim reduces
to the quadratic Taylor bound `|log (1 + u) - u| ≤ u ^ 2 / 2`, proved
below as `EarthScience.log_one_add_abs_sub_le` by monotonicity of
`log (1 + t) - t + t ^ 2 / 2` on `t ≥ 0` (its derivative is
`t ^ 2 / (1 + t) ≥ 0`). Dividing by `λ > 0` at the end gives the
remainder bound. This is first-order propagation plus a rigorous
remainder bound, not just a derivative.

## ii. Key results

- `EarthScience.log_one_add_abs_sub_le`: the quadratic Taylor bound
  for `log` at `1`.
- `EarthScience.isochron_age_slope_uncertainty`: the slope-uncertainty
  propagation bound with explicit remainder.

## iii. References

- `Real.log_le_sub_one_of_pos`, `Real.hasDerivAt_log`,
  `monotoneOn_of_deriv_nonneg` (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Quadratic Taylor bound for `Real.log` at `1`: for `u ≥ 0`,
`log (1 + u)` is within `u ^ 2 / 2` of `u`. -/
theorem log_one_add_abs_sub_le (u : ℝ) (hu : 0 ≤ u) :
    |Real.log (1 + u) - u| ≤ u ^ 2 / 2 := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hub : Real.log (1 + u) ≤ u := by
    have h := Real.log_le_sub_one_of_pos h1u
    linarith
  have hlb : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
    have hderiv : ∀ t : ℝ, 1 + t ≠ 0 →
        HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
          ((1 + t)⁻¹ - 1 + t) t := by
      intro t ht
      have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹) t := by
        have h2 := (Real.hasDerivAt_log ht).comp t
          (HasDerivAt.const_add 1 (hasDerivAt_id t))
        have h3 : (1 + t)⁻¹ * (1:ℝ) = (1 + t)⁻¹ := mul_one _
        rw [h3] at h2
        exact h2
      have hpow : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
        have h := (hasDerivAt_pow 2 t).div_const (2:ℝ)
        convert h using 1
        have e2m1 : (2:ℕ) - 1 = 1 := by norm_num
        rw [e2m1, pow_one]
        push_cast
        ring
      have h := (hlog.sub (hasDerivAt_id t)).add hpow
      exact h
    have hmem : ∀ t : ℝ, t ∈ Set.Ici (0:ℝ) → (1:ℝ) + t ≠ 0 := by
      intro t ht
      have htle : (0:ℝ) ≤ t := Set.mem_Ici.mp ht
      have hpos : (0:ℝ) < 1 + t := by linarith
      exact ne_of_gt hpos
    have hcont : ContinuousOn
        (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (Set.Ici 0) := by
      intro t ht
      exact (hderiv t (hmem t ht)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ
        (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
        (interior (Set.Ici 0)) := by
      intro t ht
      rw [interior_Ici] at ht
      have ht0 : t ∈ Set.Ici (0:ℝ) :=
        Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
      exact (hderiv t (hmem t ht0)).differentiableAt.differentiableWithinAt
    have hnn : ∀ t ∈ interior (Set.Ici (0:ℝ)),
        0 ≤ deriv (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) t := by
      intro t ht
      rw [interior_Ici] at ht
      have hpos : (0:ℝ) < t := Set.mem_Ioi.mp ht
      have ht0 : t ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (le_of_lt hpos)
      have ht' := hmem t ht0
      rw [(hderiv t ht').deriv]
      have h1t : (0:ℝ) < 1 + t := by linarith
      have heq : (1 + t)⁻¹ - 1 + t = t ^ 2 / (1 + t) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (sq_nonneg t) (le_of_lt h1t)
    have hmono : MonotoneOn
        (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (Set.Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hnn
    have hle := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    have hf0 : (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) 0 = 0 := by
      simp [Real.log_one]
    rw [hf0] at hle
    have hle' : (0:ℝ) ≤ Real.log (1 + u) - u + u ^ 2 / 2 := hle
    linarith
  have hnn : (0:ℝ) ≤ u ^ 2 / 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Propagate slope uncertainty with an explicit derivative/remainder
model: for decay constant `λ > 0`, slope `m > 0` and nonnegative slope
perturbation `δ ≥ 0`, the age change differs from the first-order
derivative term `δ / (λ * (1 + m))` by at most the explicit remainder
`δ ^ 2 / (2 * λ * (1 + m) ^ 2)`. -/
theorem isochron_age_slope_uncertainty {lam m δ : ℝ} (hlam : 0 < lam)
    (hm : 0 < m) (hδ : 0 ≤ δ) :
    |(Real.log (1 + (m + δ)) / lam - Real.log (1 + m) / lam)
        - δ / (lam * (1 + m))|
      ≤ δ ^ 2 / (2 * lam * (1 + m) ^ 2) := by
  have hA : (0:ℝ) < 1 + m := by linarith
  have hAne : (1:ℝ) + m ≠ 0 := ne_of_gt hA
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set A : ℝ := 1 + m with hAdef
  set u : ℝ := δ / A with hudef
  have hu : (0:ℝ) ≤ u := div_nonneg hδ (le_of_lt hA)
  have h1u : (0:ℝ) < 1 + u := by linarith
  have h1une : (1:ℝ) + u ≠ 0 := ne_of_gt h1u
  have hsplit : A + δ = A * (1 + u) := by
    rw [hudef]
    field_simp
  have hlog : Real.log (1 + (m + δ)) = Real.log A + Real.log (1 + u) := by
    have h1 : (1:ℝ) + (m + δ) = A + δ := by
      rw [hAdef]
      ring
    rw [h1, hsplit, Real.log_mul hAne h1une]
  have key : |Real.log (1 + u) - u| ≤ u ^ 2 / 2 :=
    log_one_add_abs_sub_le u hu
  have eu : δ / (lam * A) = u / lam := by
    rw [hudef]
    field_simp
  have e1 : (Real.log (1 + (m + δ)) / lam - Real.log A / lam) - δ / (lam * A)
      = (Real.log (1 + u) - u) / lam := by
    rw [hlog, eu]
    field_simp
    ring
  have e2 : δ ^ 2 / (2 * lam * A ^ 2) = (u ^ 2 / 2) / lam := by
    rw [hudef]
    field_simp
  rw [e1, abs_div, abs_of_pos hlam, e2]
  have hlaminv : (0:ℝ) ≤ lam⁻¹ := inv_nonneg.mpr (le_of_lt hlam)
  have h2 := mul_le_mul_of_nonneg_right key hlaminv
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h2

end EarthScience
