/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Seismic rays: travel times and Snell's law

A straight segment of length `L` in constant speed `v > 0` has travel
time `L / v`; for a two-layer ray, stationary travel time gives
`sin θ₁ / v₁ = sin θ₂ / v₂` on an interior admissible path.

## i. Overview

The two-layer travel-time functional for a source at depth `a`, a receiver
at depth `b`, interface distance `D`, and interior refraction point `x` is
`T(x) = √(a² + x²) / v₁ + √(b² + (D - x)²) / v₂`. Stationarity
(`T'(x) = 0`) gives Snell's law with `sin θ₁ = x / √(a² + x²)` and
`sin θ₂ = (D - x) / √(b² + (D - x)²)`, angles from the normal, planar
interface, positive speeds. High-frequency ray model stipulated;
critical and reflected branches are not modeled here. The equal-speed
corollary needs a nonzero common speed `v ≠ 0`.

## ii. Key results

- `EarthScience.travel_time_segment`: travel time `L / v` is nonnegative
  and `* v` recovers `L`.
- `EarthScience.snell_from_stationary`: stationarity implies Snell's law.
- `EarthScience.snell_equal_speed`: equal speeds cancel the common factor.

## iii. Table of contents

- A. Straight-segment travel time
- B. Snell's law from stationarity

## iv. References

- R. P. Feynman, R. B. Leighton, M. Sands, *The Feynman Lectures on Physics*, Vol. I,
  Addison-Wesley, 1963, Chapter 26 (§26-3: Snell's law from the least travel time of a
  ray crossing an interface, angles measured from the normal; §26-5: the stationary-time
  form of Fermat's principle).
- P. M. Shearer, *Introduction to Seismology*, 2nd ed., Cambridge University Press,
  2009, Chapter 4 (ray theory and travel times; Snell's law for seismic rays).
- `HasDerivAt.sqrt`, `HasDerivAt.unique` in Mathlib.

## A. Straight-segment travel time
-/

@[expose] public section

namespace EarthScience

/-- Straight segment: travel time `L / v` is nonnegative and `* v` recovers `L`. -/
theorem travel_time_segment {L v : ℝ} (hv : 0 < v) (hL : 0 ≤ L) :
    0 ≤ L / v ∧ L / v * v = L := by
  exact ⟨div_nonneg hL hv.le, div_mul_cancel₀ L hv.ne'⟩

/-! ## B. Snell's law from stationarity -/

set_option linter.unusedVariables false in
/-- Snell's law from stationarity: if the two-layer travel-time functional
is stationary at an interior refraction point, then
`sin θ₁ / v₁ = sin θ₂ / v₂`, with `sin θ₁ = x / √(a² + x²)` and
`sin θ₂ = (D - x) / √(b² + (D - x)²)`. -/
theorem snell_from_stationary {a b D v₁ v₂ x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hx : 0 < x) (hxD : x < D)
    (hstat : HasDerivAt
      (fun x => Real.sqrt (a ^ 2 + x ^ 2) / v₁ + Real.sqrt (b ^ 2 + (D - x) ^ 2) / v₂) 0 x) :
    x / (v₁ * Real.sqrt (a ^ 2 + x ^ 2))
      = (D - x) / (v₂ * Real.sqrt (b ^ 2 + (D - x) ^ 2)) := by
  have h1 : 0 < a ^ 2 + x ^ 2 := by
    have h1a : 0 < a ^ 2 := pow_pos ha 2
    have h1b : 0 ≤ x ^ 2 := sq_nonneg x
    linarith
  have h2 : 0 < b ^ 2 + (D - x) ^ 2 := by
    have h2a : 0 < b ^ 2 := pow_pos hb 2
    have h2b : 0 ≤ (D - x) ^ 2 := sq_nonneg _
    linarith
  have hinner1 := (hasDerivAt_pow 2 x).const_add (a ^ 2)
  have hsqrt1 := hinner1.sqrt (ne_of_gt h1)
  have hdiv1 := hsqrt1.div_const v₁
  have hDx : HasDerivAt (fun x : ℝ => D - x) (-1) x := (hasDerivAt_id x).const_sub D
  have hsq2 := hDx.fun_pow 2
  have hinner2 := hsq2.const_add (b ^ 2)
  have hsqrt2 := hinner2.sqrt (ne_of_gt h2)
  have hdiv2 := hsqrt2.div_const v₂
  have hnew := hdiv1.fun_add hdiv2
  have hE0 := hnew.unique hstat
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hE0
  have hs1 : Real.sqrt (a ^ 2 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  have hs2 : Real.sqrt (b ^ 2 + (D - x) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2)
  have hv1' : v₁ ≠ 0 := ne_of_gt hv₁
  have hv2' : v₂ ≠ 0 := ne_of_gt hv₂
  have h2s1 : (2 : ℝ) * Real.sqrt (a ^ 2 + x ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hs1
  have h2s2 : (2 : ℝ) * Real.sqrt (b ^ 2 + (D - x) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hs2
  field_simp at hE0 ⊢
  linarith

/-- Equal speeds: Snell's law gives equal ray parameters for a nonzero
common speed `v`. -/
theorem snell_equal_speed {a b D v x : ℝ} (hv : v ≠ 0)
    (hsnell : x / (v * Real.sqrt (a ^ 2 + x ^ 2))
      = (D - x) / (v * Real.sqrt (b ^ 2 + (D - x) ^ 2))) :
    x / Real.sqrt (a ^ 2 + x ^ 2) = (D - x) / Real.sqrt (b ^ 2 + (D - x) ^ 2) := by
  have e1 : x / (v * Real.sqrt (a ^ 2 + x ^ 2))
      = (x / Real.sqrt (a ^ 2 + x ^ 2)) / v := by
    rw [mul_comm v _, div_mul_eq_div_div]
  have e2 : (D - x) / (v * Real.sqrt (b ^ 2 + (D - x) ^ 2))
      = ((D - x) / Real.sqrt (b ^ 2 + (D - x) ^ 2)) / v := by
    rw [mul_comm v _, div_mul_eq_div_div]
  rw [e1, e2] at hsnell
  have h2 : (x / Real.sqrt (a ^ 2 + x ^ 2) / v) * v
      = ((D - x) / Real.sqrt (b ^ 2 + (D - x) ^ 2) / v) * v :=
    congrArg (fun t => t * v) hsnell
  rw [div_mul_cancel₀ _ hv, div_mul_cancel₀ _ hv] at h2
  exact h2

end EarthScience
