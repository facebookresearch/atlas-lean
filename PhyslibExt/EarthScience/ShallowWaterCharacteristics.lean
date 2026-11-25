/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Shallow-water characteristic speeds

For `0 ≤ g * h`, the primitive shallow-water coefficient matrix
`!![u, h; g, u]` has characteristic speeds `u - √(g h)` and
`u + √(g h)`, counted with multiplicity. The speeds are distinct
exactly when `0 < g * h`, and for `0 < g` and `h < 0` there is no real
characteristic speed.

## i. Overview

One horizontal dimension, flat frictionless bed, no rotation, constant
gravitational acceleration `g`. Fields are functions of time first,
then space: `h t x` is the total depth and `u t x` the depth-averaged
velocity, positive towards increasing `x`. The primitive form, exactly
as in `EarthScience.shallow_water_conservative_iff_primitive`, is
`hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0`. For the state
`W = (h, u)`, depth first, this is the quasilinear system
`∂ₜW + A(W) ∂ₓW = 0` with primitive coefficient matrix
`A = !![u, h; g, u]`; the bridge lemma ties the matrix to the primitive
equations, so it is not a free choice. At rest (`u = 0`, `h = H`) the
speeds are `±√(g H)`, the wave speed of
`EarthScience.shallow_water_wave_speed`.

Characteristic speeds are the real roots of the characteristic
polynomial, counted with multiplicity. The vectors `(h, ±√(g h))`
satisfy the right-eigenvector relations for the two speeds; they are
nonzero, hence characteristic directions, exactly when `h ≠ 0`. At
`h = 0` both vectors are zero and both speeds equal `u`; for `g ≠ 0`
the dry-state matrix is a Jordan block with the single direction
`(0, 1)`. Real speeds need only `0 ≤ g * h`; distinctness needs
`0 < g * h`. `Real.sqrt` is totalized, and it appears in statements
only under a hypothesis that makes its argument nonnegative.

Pointwise algebra of one explicit `2 × 2` matrix: no general
hyperbolic-system spectral theorem, no solution existence, and no
weak, shock, or entropy theory.

## ii. Key results

- `EarthScience.shallowWaterPrimitiveMatrix`: the coefficient matrix.
- `EarthScience.shallow_water_primitive_iff_quasilinear`: the primitive
  equations are the quasilinear system for that matrix.
- `EarthScience.shallow_water_characteristic_speeds`: the speeds are
  `u ± √(g h)` with multiplicity.
- `EarthScience.shallow_water_characteristic_eigenvectors`: the
  right-eigenvector relations.
- `EarthScience.shallow_water_characteristic_speeds_nodup_iff`: the
  speeds are distinct exactly at positive depth.
- `EarthScience.shallow_water_no_real_characteristic_speeds`: no real
  speed when `g * h < 0`.

## iii. Table of contents

- A. Primitive coefficient matrix and bridge
- B. Characteristic speeds and directions

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press (2017), Ch. 3, §3.1 (3.1.1, 3.1.2), for
  the shallow-water equations, as cited by
  `PhyslibExt.EarthScience.ShallowWaterNonlinear`. The speeds and
  eigenvectors here are derived from that locked primitive form.
- `EarthScience.shallow_water_conservative_iff_primitive` and
  `EarthScience.shallow_water_wave_speed`.

## A. Primitive coefficient matrix and bridge
-/

@[expose] public section

namespace EarthScience

open Matrix Polynomial

/-- The primitive coefficient matrix `A(h, u) = !![u, h; g, u]` of 1D
flat-bed shallow water for the state `(h, u)`, depth first: the
primitive form is `∂ₜ(h, u) + A ∂ₓ(h, u) = 0`. -/
def shallowWaterPrimitiveMatrix (g h u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u, h; g, u]

/-- Bridge to the primitive form. At a point `(t, x)`, for any real `hₜ`, `hₓ`,
`uₜ`, `uₓ` (in use, the slice partials there), the two primitive shallow-water
equations, written exactly as in the conservative/primitive
equivalence, hold if and only if the quasilinear system
`∂ₜW + A ∂ₓW = 0` holds for `W = (h, u)` and the primitive coefficient
matrix `A` evaluated at `(h t x, u t x)`. No premise on `g` or `h`. -/
lemma shallow_water_primitive_iff_quasilinear
    {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ} :
    (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
      uₜ + u t x * uₓ + g * hₓ = 0) ↔
    ![hₜ, uₜ] + shallowWaterPrimitiveMatrix g (h t x) (u t x) *ᵥ ![hₓ, uₓ] = 0 := by
  unfold shallowWaterPrimitiveMatrix
  constructor
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i
    · simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero]
      linarith
    · simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one]
      linarith
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    constructor <;> linarith

/-! ## B. Characteristic speeds and directions -/

/-- Characteristic speeds. If `0 ≤ g * h` (in particular for positive
gravity and depth), the real roots of the characteristic polynomial
of the primitive coefficient matrix, counted with multiplicity, are
exactly `u - √(g h)` and `u + √(g h)`. -/
theorem shallow_water_characteristic_speeds {g h u : ℝ} (hgh : 0 ≤ g * h) :
    (shallowWaterPrimitiveMatrix g h u).charpoly.roots =
      {u - √(g * h), u + √(g * h)} := by
  unfold shallowWaterPrimitiveMatrix
  set s : ℝ := √(g * h) with hs
  have hsq_mul : s * s = g * h := Real.mul_self_sqrt hgh
  have hmul : (u - s) * (u + s) = u * u - h * g := by
    linear_combination -hsq_mul
  have hsum : (u - s) + (u + s) = u + u := by ring
  have hchar : (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly
      = Polynomial.X ^ 2 - Polynomial.C (u + u) * Polynomial.X
        + Polynomial.C (u * u - h * g) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have hCadd : (Polynomial.C (u - s) : ℝ[X]) + Polynomial.C (u + s)
      = Polynomial.C (u + u) := by
    rw [← Polynomial.C_add, hsum]
  have hCmul : (Polynomial.C (u - s) : ℝ[X]) * Polynomial.C (u + s)
      = Polynomial.C (u * u - h * g) := by
    rw [← Polynomial.C_mul, hmul]
  have hfac : (Polynomial.X - Polynomial.C (u - s)) * (Polynomial.X - Polynomial.C (u + s))
      = Polynomial.X ^ 2 - Polynomial.C (u + u) * Polynomial.X
        + Polynomial.C (u * u - h * g) := by
    calc (Polynomial.X - Polynomial.C (u - s)) * (Polynomial.X - Polynomial.C (u + s))
        = Polynomial.X ^ 2 - (Polynomial.C (u - s) + Polynomial.C (u + s)) * Polynomial.X
          + Polynomial.C (u - s) * Polynomial.C (u + s) := by ring
      _ = Polynomial.X ^ 2 - Polynomial.C (u + u) * Polynomial.X
          + Polynomial.C (u * u - h * g) := by rw [hCadd, hCmul]
  have hcharfac : (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly
      = (Polynomial.X - Polynomial.C (u - s)) * (Polynomial.X - Polynomial.C (u + s)) := by
    rw [hchar, ← hfac]
  have hne1 : (Polynomial.X - Polynomial.C (u - s) : ℝ[X]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hne2 : (Polynomial.X - Polynomial.C (u + s) : ℝ[X]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hne : (Polynomial.X - Polynomial.C (u - s)) * (Polynomial.X - Polynomial.C (u + s))
      ≠ 0 := mul_ne_zero hne1 hne2
  rw [hcharfac, Polynomial.roots_mul hne, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

/-- Characteristic directions. If `0 ≤ g * h`, the vectors
`(h, √(g h))` and `(h, -√(g h))` satisfy the right-eigenvector
relations of the primitive coefficient matrix for the speeds
`u + √(g h)` and `u - √(g h)`. The two vectors are nonzero exactly
when `h ≠ 0`; at `h = 0` both are the zero vector and the relations
are trivial. -/
lemma shallow_water_characteristic_eigenvectors {g h u : ℝ}
    (hgh : 0 ≤ g * h) :
    shallowWaterPrimitiveMatrix g h u *ᵥ ![h, √(g * h)] =
        (u + √(g * h)) • ![h, √(g * h)] ∧
      shallowWaterPrimitiveMatrix g h u *ᵥ ![h, -√(g * h)] =
        (u - √(g * h)) • ![h, -√(g * h)] := by
  unfold shallowWaterPrimitiveMatrix
  have hsq : √(g * h) * √(g * h) = g * h := Real.mul_self_sqrt hgh
  constructor
  · ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      linear_combination -hsq
  · ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      linear_combination -hsq

/-- Distinct speeds exactly at positive depth. For positive gravity and
nonnegative depth, the two characteristic speeds are distinct (the
root multiset has no repeated element) if and only if the depth is
positive; at zero depth both speeds equal `u`. -/
lemma shallow_water_characteristic_speeds_nodup_iff {g h u : ℝ}
    (hg : 0 < g) (hh : 0 ≤ h) :
    (shallowWaterPrimitiveMatrix g h u).charpoly.roots.Nodup ↔ 0 < h := by
  have hgh : 0 ≤ g * h := mul_nonneg hg.le hh
  rw [shallow_water_characteristic_speeds hgh]
  have hnodup : ({u - √(g * h), u + √(g * h)} : Multiset ℝ).Nodup
      ↔ u - √(g * h) ≠ u + √(g * h) := by
    simp [Multiset.nodup_cons, Multiset.mem_singleton]
  rw [hnodup]
  have heq : (u - √(g * h) = u + √(g * h)) ↔ √(g * h) = 0 := by
    constructor
    · intro h; linarith
    · intro h; rw [h]; ring
  have hsqrt0 : (√(g * h) = 0) ↔ g * h = 0 := Real.sqrt_eq_zero hgh
  have hpos : 0 < g * h ↔ 0 < h := mul_pos_iff_of_pos_left hg
  have hnepos : (g * h ≠ 0) ↔ 0 < g * h := by
    constructor
    · intro hne
      exact lt_of_le_of_ne hgh (Ne.symm hne)
    · intro hpos2
      exact ne_of_gt hpos2
  have hne : (u - √(g * h) ≠ u + √(g * h)) ↔ √(g * h) ≠ 0 := not_congr heq
  have hsqrtne : (√(g * h) ≠ 0) ↔ g * h ≠ 0 := not_congr hsqrt0
  rw [hne, hsqrtne, hnepos, hpos]

/-- No real characteristic speeds when `g * h < 0` (for positive
gravity, negative depth): the characteristic polynomial of the
primitive coefficient matrix has no real root, so the system is not
hyperbolic there. -/
lemma shallow_water_no_real_characteristic_speeds {g h u : ℝ}
    (hgh : g * h < 0) :
    (shallowWaterPrimitiveMatrix g h u).charpoly.roots = 0 := by
  unfold shallowWaterPrimitiveMatrix
  have hchar : (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly
      = Polynomial.X ^ 2 - Polynomial.C (u + u) * Polynomial.X
        + Polynomial.C (u * u - h * g) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have hne : (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [Polynomial.mem_roots hne] at hx
  have heval : Polynomial.eval x (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly
      = (x - u) ^ 2 - g * h := by
    rw [hchar]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hpos : 0 < Polynomial.eval x (!![u, h; g, u] : Matrix (Fin 2) (Fin 2) ℝ).charpoly := by
    rw [heval]
    have hsq : (0 : ℝ) ≤ (x - u) ^ 2 := sq_nonneg _
    have hneg : (0 : ℝ) < -(g * h) := neg_pos.mpr hgh
    have h := add_pos_of_nonneg_of_pos hsq hneg
    rw [sub_eq_add_neg]
    exact h
  rw [Polynomial.IsRoot.def] at hx
  linarith

end EarthScience
