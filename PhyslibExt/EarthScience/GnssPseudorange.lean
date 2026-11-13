/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.InnerProductSpace.NormDerivative

/-!
# GNSS positioning and geodetic observations

## i. Overview

The pseudorange of satellite `j` at receiver position `x` is `r_j = ‖x - s_j‖ + b`: the geometric
range plus the receiver clock bias `b`, the receiver clock offset times the speed of light, so `b`
is in length units. Positions are in one fixed Earth-centered frame at one epoch, and the other
error terms (satellite clock, atmosphere, noise) are omitted, as for the error-free pseudoranges of
Kaplan–Hegarty, Section 7.3.1. Positions are points of `EuclideanSpace ℝ (Fin 3)`, so `‖·‖` is
the Euclidean norm and `⟪·, ·⟫_ℝ` the Euclidean inner product.

At `x₀ ≠ s_j` the first-order Jacobian row of `r_j` with respect to `(x, b)` is
`[(x₀ - s_j) / ‖x₀ - s_j‖, 1]`, proved here as the directional derivative along any `(d, db)`.
Its position part is the gradient of `‖x - s_j‖`, the unit vector from the satellite toward the
receiver. Kaplan–Hegarty, Section 7.3.1, write the same linearization with rows `(a_j, 1)` built
from the opposite unit vector `a_j = (s_j - x₀) / ‖s_j - x₀‖`, from the receiver toward the
satellite, with the offset vectors signed to match.

## ii. Key results

- `EarthScience.gnss_directional_derivative`: directional derivative is the Jacobian row dotted
  with the direction.
- `EarthScience.gnss_row_dot_algebraic_identity`: the algebraic identity
  `⟪‖x₀ - s‖⁻¹ • (x₀ - s), d⟫_ℝ + 1 * db = ⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db` for all `x₀` and `s`.
  It asserts no derivative; reading its left side as the Jacobian row dotted with `(d, db)` needs
  `x₀ ≠ s`, as in `gnss_directional_derivative`.

## iii. Table of contents

- A. Pseudorange Jacobian

## iv. References

- E. D. Kaplan and C. J. Hegarty (eds.), *Understanding GPS: Principles and Applications*,
  2nd ed., Artech House (2006). Section 2.4.1: the pseudorange is the geometric
  satellite-to-user range plus the receiver clock offset times the speed of light. Section 2.4.2:
  linearization of the pseudorange equations about an approximate user position and clock bias.
  Section 7.3.1, Eqs. (7.30)–(7.31): the linearization matrix with rows `(a_i, 1)`, where `a_i` is
  the unit vector from the linearization point toward satellite `i`.
- `MathlibExt.Analysis.InnerProductSpace.NormDerivative.HasDerivAt.norm`: the derivative of the
  norm along a curve.
-/

@[expose] public section

namespace EarthScience

open scoped InnerProductSpace

/-- GNSS pseudorange directional derivative: for receiver `x₀`, satellite `s`, `x₀ ≠ s`,
direction `d` and clock rate `db`, the pseudorange `r(t) = ‖x₀ + t • d - s‖ + (b₀ + t * db)`
has derivative at `0` equal to `⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db`, i.e. the Jacobian row
`[(x₀ - s) / ‖x₀ - s‖, 1]` dotted with `(d, db)`. -/
theorem gnss_directional_derivative (x₀ s d : EuclideanSpace ℝ (Fin 3)) (b₀ db : ℝ)
    (h : x₀ ≠ s) :
    HasDerivAt (fun t : ℝ => ‖x₀ + t • d - s‖ + (b₀ + t * db))
      (⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db) 0 := by
  have hf : HasDerivAt (fun t : ℝ => x₀ + t • d - s) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x₀).sub_const s
  have h0 : x₀ + (0 : ℝ) • d - s ≠ 0 := by
    simpa [sub_eq_zero] using h
  have hnorm :=
    MathlibExt.Analysis.InnerProductSpace.NormDerivative.HasDerivAt.norm (K := ℝ) hf h0
  have hclk : HasDerivAt (fun t : ℝ => b₀ + t * db) db 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const db).const_add b₀
  convert hnorm.add hclk using 1
  simp

/-- Purely algebraic row-dot identity, for all `x₀` and `s`: the row
`[‖x₀ - s‖⁻¹ • (x₀ - s), 1]` dotted with `(d, db)` is `⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db`.

It asserts no Jacobian or derivative. Only for `x₀ ≠ s` is this row the pseudorange Jacobian
row, by `gnss_directional_derivative`. At `x₀ = s` both sides equal `db` because `‖0‖⁻¹ = 0`,
while the range term `‖t • d‖ = |t| * ‖d‖` is not differentiable at `0` for `d ≠ 0`. -/
theorem gnss_row_dot_algebraic_identity (x₀ s d : EuclideanSpace ℝ (Fin 3)) (db : ℝ) :
    ⟪‖x₀ - s‖⁻¹ • (x₀ - s), d⟫_ℝ + 1 * db = ⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db := by
  rw [real_inner_smul_left]
  ring

end EarthScience
