/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Radial force resultant of the Boussinesq vertical stress

At every positive depth, the Boussinesq vertical stress under a
concentrated surface load `P` has radial resultant `P`:
`∫₀^∞ 2 π r σ_z(r, z) dr = P`.

## i. Overview

The stress formula is the explicit Boussinesq point-load solution as
reported by Love: a single weight `W = P` at the origin of the free
plane of a linear, homogeneous, isotropic elastic half-space produces,
across each horizontal plane `z = const`, the vertical traction
`3 W z³ / (2 π R⁵)` with `R` the distance from the load point. The
expression contains no elastic constant. The formula is supplied as a
definition from that source; it is not derived here.

The origin is at the load point on the free surface `z = 0`; `z` is
depth, positive into the half-space. The radius `r` is the horizontal
distance from the load axis, physically `r ≥ 0`, and the resultant
integrates over `r ∈ (0, ∞)`. The load `P` is a concentrated normal
surface load, physically `P > 0`; the statements are linear in `P` and
are stated for every real `P`. The stress is compression-positive, the
geotechnical sign; the tension-positive elasticity component is its
negative and is not defined here. Units: `P` is a force, `r` and `z`
are lengths, the stress is a force per area, and the resultant is a
force.

The power `(r ^ 2 + z ^ 2) ^ (5 / 2 : ℝ)` is `Real.rpow` of a
nonnegative base and agrees with `R⁵`. Division is Lean's totalized
division: at `r = z = 0` the definition returns `0`, outside the
positive-depth domain. The Bochner integral returns `0` for a
non-integrable integrand, so integrability of the radial density is a
separate result.

Excluded: the elastic half-space Green function, the full stress
tensor and displacements, and identification of the radial integral
with the integral over the horizontal plane, which needs a separate
polar-measure bridge.

## ii. Key results

- `EarthScience.boussinesqVerticalStress`: the vertical normal stress.
- `EarthScience.boussinesqVerticalStress_eq_love`: the `rpow` form
  equals Love's `3 P z³ / (2 π R⁵)` form.
- `EarthScience.boussinesqVerticalStress_zero_radius`: on the load
  axis the stress is `3 P / (2 π z²)`.
- `EarthScience.hasDerivAt_boussinesq_antiderivative` and
  `EarthScience.tendsto_boussinesq_antiderivative_atTop`: the radial
  antiderivative and its far-field limit.
- `EarthScience.integrableOn_boussinesq_resultant`: the radial density
  is integrable on `(0, ∞)`.
- `EarthScience.integral_boussinesq_resultant`: at every depth
  `z > 0` the radial resultant equals `P`.
- `EarthScience.integral_boussinesq_resultant_zero_load` and
  `EarthScience.integral_boussinesq_resultant_zero_depth`: the zero-load
  and surface controls.

## iii. Table of contents

- A. Vertical stress and radial antiderivative
- B. Integrability and the radial resultant

## iv. References

- A. E. H. Love, *A Treatise on the Mathematical Theory of
  Elasticity*, Vol. I (1892), Ch. IX, art. 162, eq. (65), p. 270.
- J. Boussinesq, *Applications des potentiels*, 1885, as reported by
  Love.

## A. Vertical stress and radial antiderivative
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace EarthScience

/-- Boussinesq vertical normal stress `σ_z(r, z) = 3 P z³ / (2 π R⁵)`,
`R² = r² + z²`, compression-positive, at depth `z` and horizontal
radius `r` under a concentrated normal surface load `P` (Love 1892,
art. 162, eq. (65)). Physically meaningful for `z > 0`; at
`r = z = 0` the totalized division returns `0`. -/
noncomputable def boussinesqVerticalStress (P r z : ℝ) : ℝ :=
  3 * P * z ^ 3 / (2 * π * (r ^ 2 + z ^ 2) ^ (5 / 2 : ℝ))

/-- Source-form bridge: the pinned `rpow` form equals Love's form
`3 P z³ / (2 π R⁵)` with `R = √(r² + z²)` the distance from the load
point. Stated for all real arguments (both sides are `0` at
`r = z = 0`, with the convention `x / 0 = 0`); the physical domain is `z > 0`. -/
lemma boussinesqVerticalStress_eq_love (P r z : ℝ) :
    boussinesqVerticalStress P r z
      = 3 * P * z ^ 3 / (2 * π * (√(r ^ 2 + z ^ 2)) ^ 5) := by
  have hnonneg : (0 : ℝ) ≤ r ^ 2 + z ^ 2 := by positivity
  have hbase : (r ^ 2 + z ^ 2) ^ (5 / 2 : ℝ) = (√(r ^ 2 + z ^ 2)) ^ 5 := by
    have hsqrt : √(r ^ 2 + z ^ 2) = (r ^ 2 + z ^ 2) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    rw [hsqrt]
    have h52 : (5 / 2 : ℝ) = (1 / 2) * (((5 : ℕ)) : ℝ) := by norm_num
    rw [h52, Real.rpow_mul hnonneg, Real.rpow_natCast]
  unfold boussinesqVerticalStress
  rw [hbase]

/-- On the load axis the vertical stress at depth `z > 0` is
`3 P / (2 π z²)`; for `P = z = 1` this is the nonzero value
`3 / (2 π)`. -/
lemma boussinesqVerticalStress_zero_radius {P z : ℝ} (hz : 0 < z) :
    boussinesqVerticalStress P 0 z = 3 * P / (2 * π * z ^ 2) := by
  have e1 : ((0 : ℝ) ^ 2 + z ^ 2) = z ^ 2 := by simp
  have h1 : ((0 : ℝ) ^ 2 + z ^ 2) ^ (5 / 2 : ℝ) = z ^ 5 := by
    rw [e1]
    have e2 : (z ^ 2 : ℝ) = z ^ (((2 : ℕ)) : ℝ) := (Real.rpow_natCast z 2).symm
    rw [e2, ← Real.rpow_mul hz.le]
    have e3 : (((2 : ℕ)) : ℝ) * (5 / 2) = (((5 : ℕ)) : ℝ) := by norm_num
    rw [e3, Real.rpow_natCast]
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hd1 : (2 : ℝ) * π * z ^ 5 ≠ 0 :=
    mul_ne_zero hpi (pow_ne_zero 5 hz.ne')
  have hd2 : (2 : ℝ) * π * z ^ 2 ≠ 0 :=
    mul_ne_zero hpi (pow_ne_zero 2 hz.ne')
  unfold boussinesqVerticalStress
  rw [h1]
  field_simp

/-- `r ↦ -P z³ (r² + z²)^(-3/2)` is an antiderivative of the radial
force density `2 π r σ_z(r, z)` at every real `r`. Stated for every
real `z` (at `z = 0` both sides vanish identically; at `r = z = 0` the real power
is `0 ^ (-3/2) = 0`, by the convention `0 ^ t = 0` for `t ≠ 0`); the physical
domain is `z > 0`. -/
lemma hasDerivAt_boussinesq_antiderivative (P z r : ℝ) :
    HasDerivAt (fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
      (2 * π * r * boussinesqVerticalStress P r z) r := by
  by_cases hz : z = 0
  · subst hz
    have hfun : (fun r : ℝ => -P * (0 : ℝ) ^ 3 * (r ^ 2 + (0 : ℝ) ^ 2) ^ (-3 / 2 : ℝ))
        = fun _ => 0 := by
      funext r
      simp
    have hrhs : 2 * π * r * boussinesqVerticalStress P r 0 = 0 := by
      simp [boussinesqVerticalStress]
    rw [hfun, hrhs]
    exact hasDerivAt_const r 0
  · have hpos : ∀ r : ℝ, (0 : ℝ) < r ^ 2 + z ^ 2 := fun r => by
      have h1 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
      have h2 : (0 : ℝ) < z ^ 2 := sq_pos_of_ne_zero hz
      linarith
    have h_inner : HasDerivAt (fun r : ℝ => r ^ 2 + z ^ 2) (2 * r) r := by
      have h := (hasDerivAt_pow 2 r).add_const (z ^ 2)
      simpa using h
    have h_rpow : HasDerivAt (fun r : ℝ => (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
        ((2 * r) * (-3 / 2) * (r ^ 2 + z ^ 2) ^ ((-3 / 2 : ℝ) - 1)) r := by
      exact h_inner.rpow_const (Or.inl (hpos r).ne')
    have h_full : HasDerivAt (fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
        ((-P * z ^ 3) * ((2 * r) * (-3 / 2) * (r ^ 2 + z ^ 2) ^ ((-3 / 2 : ℝ) - 1))) r := by
      exact h_rpow.const_mul (-P * z ^ 3)
    have hder : (2 : ℝ) * π * r * boussinesqVerticalStress P r z
        = (-P * z ^ 3) * ((2 * r) * (-3 / 2) * (r ^ 2 + z ^ 2) ^ ((-3 / 2 : ℝ) - 1)) := by
      have hposr : (0 : ℝ) < r ^ 2 + z ^ 2 := hpos r
      have hpi : (0 : ℝ) < 2 * π := by positivity
      have hpi_ne : (2 : ℝ) * π ≠ 0 := hpi.ne'
      have hexp : (-3 / 2 : ℝ) - 1 = -5 / 2 := by norm_num
      rw [hexp]
      have hinv : ((r ^ 2 + z ^ 2) ^ (5 / 2 : ℝ))⁻¹ = (r ^ 2 + z ^ 2) ^ (-5 / 2 : ℝ) := by
        have h := Real.rpow_neg (le_of_lt hposr) (5 / 2 : ℝ)
        rw [show (-(5 / 2) : ℝ) = -5 / 2 by ring] at h
        exact h.symm
      simp only [boussinesqVerticalStress]
      rw [div_eq_mul_inv, mul_inv, hinv]
      field_simp
    rw [hder]
    exact h_full

/-- The radial antiderivative `-P z³ (r² + z²)^(-3/2)` tends to `0` as
the radius tends to infinity (the far-field endpoint value). -/
lemma tendsto_boussinesq_antiderivative_atTop (P z : ℝ) :
    Tendsto (fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun r : ℝ => r ^ 2 + z ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (z ^ 2)
      (tendsto_pow_atTop (n := 2) two_ne_zero)
  have hrpow : Tendsto (fun r : ℝ => (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (y := (3 / 2 : ℝ)) (by norm_num)
    have hcomp : Tendsto (fun r : ℝ => (r ^ 2 + z ^ 2) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      hpow.comp hbase
    simpa [show (-(3 / 2) : ℝ) = -3 / 2 by ring] using hcomp
  have hmul := hrpow.const_mul (-P * z ^ 3)
  simpa using hmul

/-! ## B. Integrability and the radial resultant -/

/-- The radial force density `2 π r σ_z(r, z)` is Lebesgue integrable over `r ∈ (0, ∞)`, so the
resultant below is a genuine (not totalized) integral. Stated for every real `z`; the physical
domain is `z > 0`. So the radial force resultant is the integral of an integrable function, not the
value `0` that the convention gives to the integral of a non-integrable one. -/
lemma integrableOn_boussinesq_resultant (P z : ℝ) :
    IntegrableOn (fun r : ℝ => 2 * π * r * boussinesqVerticalStress P r z)
      (Ioi 0) := by
  have hcont : ContinuousWithinAt
      (fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ)) (Ici 0) 0 :=
    (hasDerivAt_boussinesq_antiderivative P z 0).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
      (2 * π * x * boussinesqVerticalStress P x z) x :=
    fun x _ => hasDerivAt_boussinesq_antiderivative P z x
  have heq : ∀ x : ℝ, 0 < x →
      2 * π * x * boussinesqVerticalStress P x z
        = x * (3 * (P * z ^ 3) / (x ^ 2 + z ^ 2) ^ (5 / 2 : ℝ)) := by
    intro x hx
    have hx2 : (0 : ℝ) < x ^ 2 + z ^ 2 := by
      have h1 : (0 : ℝ) < x ^ 2 := pow_pos hx 2
      have h2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
      linarith
    have hB : (x ^ 2 + z ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
      (rpow_pos_of_pos hx2 _).ne'
    have hpi : (2 : ℝ) * π ≠ 0 := by positivity
    have hd : (2 : ℝ) * π * (x ^ 2 + z ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
      mul_ne_zero hpi hB
    simp only [boussinesqVerticalStress]
    field_simp
  have hbase : ∀ x : ℝ, 0 < x → (0 : ℝ) ≤ (x ^ 2 + z ^ 2) ^ (5 / 2 : ℝ) := by
    intro x hx
    have hx2 : (0 : ℝ) < x ^ 2 + z ^ 2 := by
      have h1 : (0 : ℝ) < x ^ 2 := pow_pos hx 2
      have h2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
      linarith
    exact (rpow_pos_of_pos hx2 _).le
  by_cases hsign : (0 : ℝ) ≤ P * z ^ 3
  · refine integrableOn_Ioi_deriv_of_nonneg (l := 0) hcont hderiv ?_ ?_
    · intro x hx
      have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
      show (0 : ℝ) ≤ 2 * π * x * boussinesqVerticalStress P x z
      rw [heq x hx0]
      exact mul_nonneg hx0.le (div_nonneg (mul_nonneg (by norm_num) hsign) (hbase x hx0))
    · exact tendsto_boussinesq_antiderivative_atTop P z
  · refine integrableOn_Ioi_deriv_of_nonpos (l := 0) hcont hderiv ?_ ?_
    · intro x hx
      have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
      have hneg : P * z ^ 3 ≤ 0 := le_of_not_ge hsign
      show 2 * π * x * boussinesqVerticalStress P x z ≤ 0
      rw [heq x hx0]
      exact mul_nonpos_of_nonneg_of_nonpos hx0.le
        (div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg) (hbase x hx0))
    · exact tendsto_boussinesq_antiderivative_atTop P z

/-- **Radial force resultant.** At every depth `z > 0` the vertical
stress integrated over the horizontal plane in radial form,
`∫₀^∞ 2 π r σ_z(r, z) dr`, equals the applied load `P`. This is the
one-dimensional radial integral only; its equality with the planar
integral is excluded. -/
theorem integral_boussinesq_resultant {P z : ℝ} (hz : 0 < z) :
    ∫ r in Ioi 0, 2 * π * r * boussinesqVerticalStress P r z = P := by
  have hval : -P * z ^ 3 * ((0 : ℝ) ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ) = -P := by
    have e1 : ((0 : ℝ) ^ 2 + z ^ 2) = z ^ 2 := by simp
    have e2 : (z ^ 2 : ℝ) = z ^ (((2 : ℕ)) : ℝ) := (Real.rpow_natCast z 2).symm
    have e3 : (((2 : ℕ)) : ℝ) * (-3 / 2) = -(((3 : ℕ)) : ℝ) := by norm_num
    have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz.ne'
    rw [e1, e2, ← Real.rpow_mul hz.le, e3, Real.rpow_neg hz.le, Real.rpow_natCast,
      mul_assoc, mul_inv_cancel₀ hz3, mul_one]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun r : ℝ => -P * z ^ 3 * (r ^ 2 + z ^ 2) ^ (-3 / 2 : ℝ))
    (f' := fun r : ℝ => 2 * π * r * boussinesqVerticalStress P r z)
    (a := 0) (m := 0)
    (fun x _ => hasDerivAt_boussinesq_antiderivative P z x)
    (integrableOn_boussinesq_resultant P z)
    (tendsto_boussinesq_antiderivative_atTop P z)
  rw [hval] at h
  simpa using h

/-- Focused check (zero load): with `P = 0` the stress vanishes and the
radial resultant is `0` at every depth. -/
lemma integral_boussinesq_resultant_zero_load (z : ℝ) :
    ∫ r in Ioi 0, 2 * π * r * boussinesqVerticalStress 0 r z = 0 := by
  have h : (fun r : ℝ => 2 * π * r * boussinesqVerticalStress 0 r z) = fun _ => 0 := by
    funext r
    simp [boussinesqVerticalStress]
  rw [h]
  simp

/-- Negative control (surface `z = 0` excluded): on the loaded surface
the formula vanishes for every `r`, so the radial resultant is `0`
and the identity `= P` fails for every `P ≠ 0`; the depth premise
`0 < z` of `integral_boussinesq_resultant` is necessary. -/
lemma integral_boussinesq_resultant_zero_depth (P : ℝ) :
    ∫ r in Ioi 0, 2 * π * r * boussinesqVerticalStress P r 0 = 0 := by
  have h : (fun r : ℝ => 2 * π * r * boussinesqVerticalStress P r 0) = fun _ => 0 := by
    funext r
    simp [boussinesqVerticalStress]
  rw [h]
  simp

end EarthScience
