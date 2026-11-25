/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Orbital perturbations: regularity of the inverse-square field

## i. Overview

Quantitative regularity for the inverse-square acceleration field away
from the collision set, for use by orbital-mechanics consumers that need
an explicit exterior Lipschitz constant without any argument through the
excluded ball.

## ii. Key results

- `OrbitalPerturbations.norm_inverseSquareField`: for `μ ≥ 0`, away from
  the origin the field has magnitude `μ / ‖r‖^2`.
- `OrbitalPerturbations.inverseSquareField_lipschitz_exterior`: for
  `μ ≥ 0`, outside the ball of radius `rmin > 0`, the field is Lipschitz
  with the conservative constant `4μ / rmin^3`.
- `OrbitalPerturbations.inverseSquareField_lipschitzOnWith`: for `μ ≥ 0`
  and `rmin > 0`, the same bound in Mathlib's bundled `LipschitzOnWith` form on
  `{r | rmin ≤ ‖r‖}`, for downstream Lipschitz API consumers.
- `OrbitalPerturbations.j2Accel_norm_le`: for `μ > 0` and `rmin > 0`, the
  J2 perturbing acceleration is bounded by `3 * |J2| * μ * R^2 / rmin^4` outside
  the ball of radius `rmin`, from the normalized squared magnitude
  `5u^2 - 2u + 1 ≤ 4` for `u = z^2 / ‖r‖^2 ∈ [0, 1]`.

## iii. Table of contents

- A. The inverse-square field on an exterior set
- B. The J2 perturbing-acceleration envelope

## iv. References

- The estimate is direct norm algebra (triangle and reverse triangle
  inequalities); no mean-value theorem through the excluded ball is
  used, so no convexity hypothesis on the exterior set appears.
- D. A. Vallado, *Fundamentals of Astrodynamics and Applications*:
  the J2 perturbing-acceleration component formulas and sign
  convention used in section B (geopotential term
  `-(μ / ‖r‖) * J2 * (R / ‖r‖)^2 * P₂(z / ‖r‖)`, positive `J2` for
  the oblate case).

## A. The inverse-square field on an exterior set

-/

@[expose] public section

namespace OrbitalPerturbations

/-- The inverse-square field `μ • r / ‖r‖^3` (outward radial form) on a real inner-product space, as the scalar multiple
`(μ / ‖r‖^3) • r`. It is intended for points away from the origin; at
`r = 0` its value is `0` (with the convention `x / 0 = 0` the scalar
factor is `0`). For `μ > 0` this field points parallel to
`r` (outward from the origin); the gravitational acceleration toward
an attracting body at the origin is its negative,
`-(μ / ‖r‖^3) • r`. -/
noncomputable def inverseSquareField {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : ℝ) (r : E) : E :=
  (μ / ‖r‖ ^ 3) • r

/-- For `μ ≥ 0`, away from the origin the inverse-square field has magnitude
`μ / ‖r‖^2`. -/
lemma norm_inverseSquareField {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : ℝ} (hμ : 0 ≤ μ) {r : E} (hr : r ≠ 0) :
    ‖inverseSquareField μ r‖ = μ / ‖r‖ ^ 2 := by
  have hr0 : ‖r‖ ≠ 0 := fun h0 => hr (norm_eq_zero.mp h0)
  have hr2 : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hr3 : ‖r‖ ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  have hnn : (0 : ℝ) ≤ μ / ‖r‖ ^ 3 := div_nonneg hμ (pow_nonneg (norm_nonneg _) _)
  unfold inverseSquareField
  rw [norm_smul, Real.norm_of_nonneg hnn]
  field_simp

/-- Exterior Lipschitz bound for the inverse-square field: for `μ ≥ 0`, outside the
excluded ball of radius `rmin > 0`, the field is Lipschitz with constant
`4μ / rmin^3`. The constant is conservative, not claimed sharp, and the
estimate is direct algebra from the reverse triangle inequality, with no
mean-value argument through the excluded ball. -/
lemma inverseSquareField_lipschitz_exterior {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ rmin : ℝ}
    (hμ : 0 ≤ μ) (hrmin : 0 < rmin) {r s : E} (hr : rmin ≤ ‖r‖)
    (hs : rmin ≤ ‖s‖) :
    ‖inverseSquareField μ r - inverseSquareField μ s‖ ≤
      (4 * μ / rmin ^ 3) * ‖r - s‖ := by
  have har0 : 0 < ‖r‖ := lt_of_lt_of_le hrmin hr
  have has0 : 0 < ‖s‖ := lt_of_lt_of_le hrmin hs
  have hnr : (0 : ℝ) ≤ ‖r‖ := har0.le
  have hns : (0 : ℝ) ≤ ‖s‖ := has0.le
  have hr0 : ‖r‖ ≠ 0 := ne_of_gt har0
  have hs0 : ‖s‖ ≠ 0 := ne_of_gt has0
  have hr2 : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hs2 : ‖s‖ ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have hr3 : ‖r‖ ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  have hs3 : ‖s‖ ^ 3 ≠ 0 := pow_ne_zero 3 hs0
  have hden1 : ‖r‖ ^ 3 * ‖s‖ ^ 3 ≠ 0 := mul_ne_zero hr3 hs3
  have hden2 : ‖r‖ ^ 3 * ‖s‖ ^ 2 ≠ 0 := mul_ne_zero hr3 hs2
  have hr1s2 : ‖r‖ * ‖s‖ ^ 2 ≠ 0 := mul_ne_zero hr0 hs2
  have hr2s1 : ‖r‖ ^ 2 * ‖s‖ ≠ 0 := mul_ne_zero hr2 hs0
  have hnn1 : (0 : ℝ) ≤ μ / ‖r‖ ^ 3 := div_nonneg hμ (pow_nonneg hnr _)
  have hsplit : inverseSquareField μ r - inverseSquareField μ s
      = (μ / ‖r‖ ^ 3) • (r - s) + ((μ / ‖r‖ ^ 3) - (μ / ‖s‖ ^ 3)) • s := by
    unfold inverseSquareField
    rw [smul_sub, sub_smul]
    abel
  have t1 : ‖(μ / ‖r‖ ^ 3) • (r - s)‖ = (μ / ‖r‖ ^ 3) * ‖r - s‖ := by
    rw [norm_smul, Real.norm_of_nonneg hnn1]
  have t2 : ‖((μ / ‖r‖ ^ 3) - (μ / ‖s‖ ^ 3)) • s‖
      = |μ / ‖r‖ ^ 3 - μ / ‖s‖ ^ 3| * ‖s‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h3r : rmin ^ 3 ≤ ‖r‖ ^ 3 := pow_le_pow_left₀ hrmin.le hr 3
  have h2s : rmin ^ 2 ≤ ‖s‖ ^ 2 := pow_le_pow_left₀ hrmin.le hs 2
  have h2r : rmin ^ 2 ≤ ‖r‖ ^ 2 := pow_le_pow_left₀ hrmin.le hr 2
  have hdiv1 : μ / ‖r‖ ^ 3 ≤ μ / rmin ^ 3 :=
    div_le_div_of_nonneg_left hμ (pow_pos hrmin 3) h3r
  have hterm1 : (μ / ‖r‖ ^ 3) * ‖r - s‖ ≤ (μ / rmin ^ 3) * ‖r - s‖ :=
    mul_le_mul_of_nonneg_right hdiv1 (norm_nonneg _)
  have hba : |‖s‖ - ‖r‖| ≤ ‖r - s‖ := by
    have h := abs_norm_sub_norm_le s r
    rwa [norm_sub_rev] at h
  have hcube : ‖s‖ ^ 3 - ‖r‖ ^ 3
      = (‖s‖ - ‖r‖) * (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2) := by ring
  have hnn2 : (0 : ℝ) ≤ ‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2 :=
    add_nonneg (add_nonneg (pow_nonneg hnr 2) (mul_nonneg hnr hns))
      (pow_nonneg hns 2)
  have habs3 : |‖s‖ ^ 3 - ‖r‖ ^ 3|
      = |‖s‖ - ‖r‖| * (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2) := by
    rw [hcube, abs_mul, abs_of_nonneg hnn2]
  have hsub : μ / ‖r‖ ^ 3 - μ / ‖s‖ ^ 3
      = μ * (‖s‖ ^ 3 - ‖r‖ ^ 3) / (‖r‖ ^ 3 * ‖s‖ ^ 3) := by
    field_simp
  have e1 : rmin ^ 3 ≤ ‖r‖ * ‖s‖ ^ 2 := by
    rw [show rmin ^ 3 = rmin * rmin ^ 2 from by ring]
    exact mul_le_mul hr h2s (pow_nonneg hrmin.le 2) hnr
  have e2 : rmin ^ 3 ≤ ‖r‖ ^ 2 * ‖s‖ := by
    rw [show rmin ^ 3 = rmin ^ 2 * rmin from by ring]
    exact mul_le_mul h2r hs hrmin.le (pow_nonneg hnr 2)
  have q1 : 1 / (‖r‖ * ‖s‖ ^ 2) ≤ 1 / rmin ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hrmin 3) e1
  have q2 : 1 / (‖r‖ ^ 2 * ‖s‖) ≤ 1 / rmin ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hrmin 3) e2
  have q3 : 1 / ‖r‖ ^ 3 ≤ 1 / rmin ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hrmin 3) h3r
  have hQ : (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2) / (‖r‖ ^ 3 * ‖s‖ ^ 2)
      ≤ 3 / rmin ^ 3 := by
    have hQsplit : (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2) / (‖r‖ ^ 3 * ‖s‖ ^ 2)
        = 1 / (‖r‖ * ‖s‖ ^ 2) + 1 / (‖r‖ ^ 2 * ‖s‖) + 1 / ‖r‖ ^ 3 := by
      field_simp
    rw [hQsplit,
      show (3 : ℝ) / rmin ^ 3 = 1 / rmin ^ 3 + 1 / rmin ^ 3 + 1 / rmin ^ 3
        from by ring]
    exact add_le_add (add_le_add q1 q2) q3
  have hterm2eq : |μ / ‖r‖ ^ 3 - μ / ‖s‖ ^ 3| * ‖s‖
      = μ * |‖s‖ - ‖r‖| * ((‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)
        / (‖r‖ ^ 3 * ‖s‖ ^ 2)) := by
    have e1' : |μ * (‖s‖ ^ 3 - ‖r‖ ^ 3)|
        = μ * (|‖s‖ - ‖r‖| * (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)) := by
      rw [abs_mul, abs_of_nonneg hμ, habs3]
    have e2' : |(‖r‖ ^ 3 * ‖s‖ ^ 3 : ℝ)| = ‖r‖ ^ 3 * ‖s‖ ^ 3 :=
      abs_of_nonneg (mul_nonneg (pow_nonneg hnr 3) (pow_nonneg hns 3))
    rw [hsub, abs_div, e1', e2']
    field_simp
  have hterm2 : |μ / ‖r‖ ^ 3 - μ / ‖s‖ ^ 3| * ‖s‖
      ≤ (3 * μ / rmin ^ 3) * ‖r - s‖ := by
    rw [hterm2eq]
    have hQnonneg : (0 : ℝ) ≤ (‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)
        / (‖r‖ ^ 3 * ‖s‖ ^ 2) :=
      div_nonneg hnn2 (mul_nonneg (pow_nonneg hnr 3) (pow_nonneg hns 2))
    have step1 : μ * |‖s‖ - ‖r‖| * ((‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)
          / (‖r‖ ^ 3 * ‖s‖ ^ 2))
        ≤ μ * ‖r - s‖ * ((‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)
          / (‖r‖ ^ 3 * ‖s‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hba hμ) hQnonneg
    have step2 : μ * ‖r - s‖ * ((‖r‖ ^ 2 + ‖r‖ * ‖s‖ + ‖s‖ ^ 2)
          / (‖r‖ ^ 3 * ‖s‖ ^ 2))
        ≤ μ * ‖r - s‖ * (3 / rmin ^ 3) :=
      mul_le_mul_of_nonneg_left hQ (mul_nonneg hμ (norm_nonneg _))
    have hfin := le_trans step1 step2
    rwa [show (3 * μ / rmin ^ 3) * ‖r - s‖ = μ * ‖r - s‖ * (3 / rmin ^ 3)
      from by ring]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [t1, t2]
  calc (μ / ‖r‖ ^ 3) * ‖r - s‖ + |μ / ‖r‖ ^ 3 - μ / ‖s‖ ^ 3| * ‖s‖
        ≤ (μ / rmin ^ 3) * ‖r - s‖ + (3 * μ / rmin ^ 3) * ‖r - s‖ :=
          add_le_add hterm1 hterm2
      _ = (4 * μ / rmin ^ 3) * ‖r - s‖ := by ring

/-- The exterior Lipschitz bound in Mathlib's standard bundled form: for `μ ≥ 0`
and `rmin > 0`, the inverse-square field is Lipschitz on the exterior set
`{r | rmin ≤ ‖r‖}` with constant `4μ / rmin^3`. This is the form
downstream `LipschitzOnWith` API consumes; the pointwise norm form is
`inverseSquareField_lipschitz_exterior`. -/
lemma inverseSquareField_lipschitzOnWith {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ rmin : ℝ}
    (hμ : 0 ≤ μ) (hrmin : 0 < rmin) :
    LipschitzOnWith
      ⟨4 * μ / rmin ^ 3,
        div_nonneg (mul_nonneg (by norm_num) hμ) (pow_nonneg hrmin.le 3)⟩
      (inverseSquareField μ) {r : E | rmin ≤ ‖r‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  simp only [Set.mem_ofPred_eq] at hx hy
  rw [dist_eq_norm, dist_eq_norm]
  exact inverseSquareField_lipschitz_exterior hμ hrmin hx hy

/-! ## B. The J2 perturbing-acceleration envelope -/

/-- The `J2` perturbing acceleration for gravitational parameter `μ`,
reference radius `R`, and signed oblateness coefficient `J2`, at a
position `r` in three-dimensional Euclidean space. With axial
coordinate `z = r 2` and `u = z^2 / ‖r‖^2`, and `ẑ = single 2 z` the
axial projection of `r`:
`a = -(3 * J2 * μ * R^2 / (2 * ‖r‖^5)) * ((1 - 5u) • r + 2 • ẑ)`.

Convention: away from the origin this is the gradient of the geopotential
term `-(μ / ‖r‖) * J2 * (R / ‖r‖)^2 * P₂(z / ‖r‖)` with Legendre
polynomial `P₂` (geodesy sign convention: the acceleration is the gradient
of the potential), so positive `J2` is the oblate case (Earth:
`J2 ≈ 1.083e-3`). This matches the component formulas in
Vallado, *Fundamentals of Astrodynamics and Applications*. The field is
read away from the origin; at `r = 0` its value is `0` (with the
convention `x / 0 = 0` the scalar factor is `0`). -/
noncomputable def j2Accel (μ R J2 : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  -(3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 5)) •
    ((1 - 5 * ((r 2) ^ 2 / ‖r‖ ^ 2)) • r +
      (2 : ℝ) • EuclideanSpace.single 2 (r 2))

/-- The normalized J2 magnitude polynomial `5u^2 - 2u + 1` is at most
`4` on `u ∈ [0, 1]` (it equals `4` at the pole `u = 1` and `1` at the
equator `u = 0`). -/
lemma j2Poly_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 5 * u ^ 2 - 2 * u + 1 ≤ 4 := by
  have h3 : (0 : ℝ) ≤ 3 + 5 * u := by linarith
  have h := mul_nonneg (sub_nonneg.mpr hu1) h3
  have hid : 5 * u ^ 2 - 2 * u + 1 = 4 - (1 - u) * (3 + 5 * u) := by ring
  rw [hid]
  linarith

/-- Squared magnitude of the J2 acceleration: for `r ≠ 0`, writing
`u = (r 2)^2 / ‖r‖^2`,
`‖a‖^2 = (3 * J2 * μ * R^2 / (2 * ‖r‖^4))^2 * (5 * u^2 - 2 * u + 1)`. -/
lemma j2Accel_norm_sq {μ R J2 : ℝ}
    {r : EuclideanSpace ℝ (Fin 3)} (hr : r ≠ 0) :
    ‖j2Accel μ R J2 r‖ ^ 2 =
      (3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)) ^ 2 *
        (5 * ((r 2) ^ 2 / ‖r‖ ^ 2) ^ 2 - 2 * ((r 2) ^ 2 / ‖r‖ ^ 2) + 1) := by
  have hnorm : ‖r‖ ≠ 0 := fun h => hr (norm_eq_zero.mp h)
  have hinner : inner ℝ r (EuclideanSpace.single 2 (r 2)) = (r 2) * (r 2) := by
    rw [EuclideanSpace.inner_single_right]
    simp
  have hsingle : ‖EuclideanSpace.single (2 : Fin 3) (r 2)‖ = ‖(r 2 : ℝ)‖ :=
    PiLp.norm_single 2 (fun _ => ℝ) 2 (r 2)
  have hn2 : (‖r‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
  have hn4 : (2 : ℝ) * ‖r‖ ^ 4 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 4 hnorm)
  have hn5 : (2 : ℝ) * ‖r‖ ^ 5 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 5 hnorm)
  unfold j2Accel
  simp only [norm_smul, mul_pow, norm_add_sq_real, real_inner_smul_left,
    real_inner_smul_right, hinner, hsingle, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- J2 acceleration envelope: for `μ > 0` and `rmin ≤ ‖r‖` with
`rmin > 0`,
`‖a_J2‖ ≤ 3 * |J2| * μ * R^2 / rmin^4`. -/
lemma j2Accel_norm_le {μ R J2 rmin : ℝ} (hμ : 0 < μ) (hrmin : 0 < rmin)
    {r : EuclideanSpace ℝ (Fin 3)} (hr : rmin ≤ ‖r‖) :
    ‖j2Accel μ R J2 r‖ ≤
      3 * |J2| * μ * R ^ 2 / rmin ^ 4 := by
  have hnpos : 0 < ‖r‖ := lt_of_lt_of_le hrmin hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hr
    linarith
  have hsq : ‖r‖ ^ 2 = (r 0) ^ 2 + (r 1) ^ 2 + (r 2) ^ 2 := by
    have h := EuclideanSpace.norm_sq_eq r
    rw [Fin.sum_univ_three] at h
    simp only [Real.norm_eq_abs, sq_abs] at h
    exact h
  have hcomp : (r 2) ^ 2 ≤ ‖r‖ ^ 2 := by
    rw [hsq]
    exact le_add_of_nonneg_left (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hu0 : 0 ≤ (r 2) ^ 2 / ‖r‖ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hu1 : (r 2) ^ 2 / ‖r‖ ^ 2 ≤ 1 := (div_le_one (pow_pos hnpos 2)).mpr hcomp
  have hP : 5 * ((r 2) ^ 2 / ‖r‖ ^ 2) ^ 2 - 2 * ((r 2) ^ 2 / ‖r‖ ^ 2) + 1 ≤ 4 :=
    j2Poly_le hu0 hu1
  have hsq2 : ‖j2Accel μ R J2 r‖ ^ 2 = (3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)) ^ 2 *
      (5 * ((r 2) ^ 2 / ‖r‖ ^ 2) ^ 2 - 2 * ((r 2) ^ 2 / ‖r‖ ^ 2) + 1) :=
    j2Accel_norm_sq hr0
  have hK2 : (0 : ℝ) ≤ (3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)) ^ 2 := sq_nonneg _
  have hAle : ‖j2Accel μ R J2 r‖ ^ 2 ≤ (2 * |3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)|) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hP hK2
    have habs : (2 * |3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)|) ^ 2
        = (3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)) ^ 2 * 4 := by
      generalize (3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)) = K
      rw [mul_pow, sq_abs]
      ring
    rw [hsq2, habs]
    exact hmul
  have hA : ‖j2Accel μ R J2 r‖ ≤ 2 * |3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)| := by
    have h := abs_le_of_sq_le_sq hAle (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  have hR2 : |R ^ 2| = R ^ 2 := abs_of_nonneg (sq_nonneg R)
  have hden : |(2 : ℝ) * ‖r‖ ^ 4| = 2 * ‖r‖ ^ 4 :=
    abs_of_pos (mul_pos two_pos (pow_pos hnpos 4))
  have hK : 2 * |3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)| = 3 * |J2| * μ * R ^ 2 / ‖r‖ ^ 4 := by
    have hne : (‖r‖ : ℝ) ≠ 0 := ne_of_gt hnpos
    have hn4 : (2 : ℝ) * ‖r‖ ^ 4 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 4 hne)
    have hn4' : (‖r‖ : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hne
    rw [abs_div, hden]
    simp only [abs_mul, h3, abs_of_pos hμ, hR2]
    field_simp
  have hX : (0 : ℝ) ≤ 3 * |J2| * μ * R ^ 2 := by positivity
  have h4 : rmin ^ 4 ≤ ‖r‖ ^ 4 := pow_le_pow_left₀ hrmin.le hr 4
  have hfin : 3 * |J2| * μ * R ^ 2 / ‖r‖ ^ 4 ≤ 3 * |J2| * μ * R ^ 2 / rmin ^ 4 := by
    have h1 : (1 : ℝ) / ‖r‖ ^ 4 ≤ 1 / rmin ^ 4 :=
      one_div_le_one_div_of_le (pow_pos hrmin 4) h4
    have h2 := mul_le_mul_of_nonneg_left h1 hX
    rw [← div_eq_mul_one_div, ← div_eq_mul_one_div] at h2
    exact h2
  calc ‖j2Accel μ R J2 r‖
      ≤ 2 * |3 * J2 * μ * R ^ 2 / (2 * ‖r‖ ^ 4)| := hA
    _ = 3 * |J2| * μ * R ^ 2 / ‖r‖ ^ 4 := hK
    _ ≤ 3 * |J2| * μ * R ^ 2 / rmin ^ 4 := hfin

end OrbitalPerturbations
