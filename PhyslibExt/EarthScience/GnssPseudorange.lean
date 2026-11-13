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
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# GNSS positioning and geodetic observations

## i. Overview

The pseudorange of satellite `j` at receiver position `x` is `r_j = ‖x - s_j‖ + b`: the geometric
range plus the receiver clock bias `b`, the receiver clock offset times the speed of light, so `b`
is in length units. Positions are in one fixed Earth-centered frame at one epoch, and the other
error terms (satellite clock, atmosphere, noise) are omitted, as for the error-free pseudoranges of
Kaplan–Hegarty, Section 7.3.1. The norm is the `Real.sqrt` of the sum of squared component
differences.

At `x₀ ≠ s_j` the first-order Jacobian row of `r_j` with respect to `(x, b)` is
`[(x₀ - s_j) / ‖x₀ - s_j‖, 1]`, proved here as the directional derivative along any `(d, db)`.
Its position part is the gradient of `‖x - s_j‖`, the unit vector from the satellite toward the
receiver. Kaplan–Hegarty, Section 7.3.1, write the same linearization with rows `(a_j, 1)` built
from the opposite unit vector `a_j = (s_j - x₀) / ‖s_j - x₀‖`, from the receiver toward the
satellite, with the offset vectors signed to match.

## ii. Key results

- `EarthScience.gnss_directional_derivative`: directional derivative is the Jacobian row dotted
  with the direction.
- `EarthScience.gnss_jacobian_row_dot`: the row-dot identity.

## iii. Table of contents

- A. Pseudorange Jacobian

## iv. References

- E. D. Kaplan and C. J. Hegarty (eds.), *Understanding GPS: Principles and Applications*,
  2nd ed., Artech House (2006). Section 2.4.1: the pseudorange is the geometric
  satellite-to-user range plus the receiver clock offset times the speed of light. Section 2.4.2:
  linearization of the pseudorange equations about an approximate user position and clock bias.
  Section 7.3.1, Eqs. (7.30)–(7.31): the linearization matrix with rows `(a_i, 1)`, where `a_i` is
  the unit vector from the linearization point toward satellite `i`.
- `HasDerivAt.sqrt`, `HasDerivAt.fun_pow` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- GNSS pseudorange directional derivative: for receiver `x₀`, satellite `s`,
`x₀ ≠ s`, direction `d` and clock-rate `db`, the pseudorange
`r(t) = ‖x₀ + t • d - s‖ + (b₀ + t * db)` (norm = `Real.sqrt` of the sum of
squared component differences) has derivative at `0` equal to
`((x₀ - s) ⬝ d) / ‖x₀ - s‖ + db`, i.e. the Jacobian row
`[(x₀ - s) / ‖x₀ - s‖, 1]` dotted with `(d, db)`. -/
theorem gnss_directional_derivative (x₀ s d : ℝ × ℝ × ℝ) (b₀ db : ℝ)
    (h : x₀ ≠ s) :
    HasDerivAt (fun t => Real.sqrt ((x₀.1 + t * d.1 - s.1) ^ 2 +
        (x₀.2.1 + t * d.2.1 - s.2.1) ^ 2 +
        (x₀.2.2 + t * d.2.2 - s.2.2) ^ 2) + (b₀ + t * db))
      (((x₀.1 - s.1) * d.1 + (x₀.2.1 - s.2.1) * d.2.1 +
        (x₀.2.2 - s.2.2) * d.2.2) /
          Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
            (x₀.2.2 - s.2.2) ^ 2) + db) 0 := by
  obtain ⟨x1, x2, x3⟩ := x₀
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨d1, d2, d3⟩ := d
  dsimp only at h ⊢
  have hpos : 0 < (x1 - s1) ^ 2 + (x2 - s2) ^ 2 + (x3 - s3) ^ 2 := by
    have n1 := sq_nonneg (x1 - s1)
    have n2 := sq_nonneg (x2 - s2)
    have n3 := sq_nonneg (x3 - s3)
    by_contra hc
    push Not at hc
    have z1 : (x1 - s1) ^ 2 = 0 := le_antisymm (by linarith) n1
    have z2 : (x2 - s2) ^ 2 = 0 := le_antisymm (by linarith) n2
    have z3 : (x3 - s3) ^ 2 = 0 := le_antisymm (by linarith) n3
    have e1 : x1 = s1 := sub_eq_zero.mp (sq_eq_zero_iff.mp z1)
    have e2 : x2 = s2 := sub_eq_zero.mp (sq_eq_zero_iff.mp z2)
    have e3 : x3 = s3 := sub_eq_zero.mp (sq_eq_zero_iff.mp z3)
    exact h (by rw [e1, e2, e3])
  have g1 : HasDerivAt (fun t : ℝ => x1 + t * d1 - s1) (1 * d1) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const d1).const_add x1).sub_const s1
  have g2 : HasDerivAt (fun t : ℝ => x2 + t * d2 - s2) (1 * d2) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const d2).const_add x2).sub_const s2
  have g3 : HasDerivAt (fun t : ℝ => x3 + t * d3 - s3) (1 * d3) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const d3).const_add x3).sub_const s3
  have hsum := ((g1.fun_pow 2).add (g2.fun_pow 2)).add (g3.fun_pow 2)
  have hne : ((((fun i : ℝ => (x1 + i * d1 - s1) ^ 2) +
      (fun i : ℝ => (x2 + i * d2 - s2) ^ 2)) +
      (fun i : ℝ => (x3 + i * d3 - s3) ^ 2))) 0 ≠ 0 := by
    have h0 := ne_of_gt hpos
    simpa using h0
  have hsqrt := hsum.sqrt hne
  have hclk : HasDerivAt (fun t : ℝ => b₀ + t * db) (1 * db) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).mul_const db).const_add b₀
  have hmain := hsqrt.add hclk
  convert hmain using 1
  simp
  field_simp

/-- The Jacobian row dotted with a perturbation equals the directional
derivative: with `n = ‖x₀ - s‖ ≠ 0`, the row
`((x₀-s)/n, 1)` dotted with `(d, db)` is `((x₀-s) ⬝ d)/n + db`. -/
theorem gnss_jacobian_row_dot (x₀ s d : ℝ × ℝ × ℝ) (db : ℝ)
    (hn : Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
      (x₀.2.2 - s.2.2) ^ 2) ≠ 0) :
    (x₀.1 - s.1) / Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
        (x₀.2.2 - s.2.2) ^ 2) * d.1 +
      (x₀.2.1 - s.2.1) / Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
        (x₀.2.2 - s.2.2) ^ 2) * d.2.1 +
      (x₀.2.2 - s.2.2) / Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
        (x₀.2.2 - s.2.2) ^ 2) * d.2.2 + 1 * db =
    ((x₀.1 - s.1) * d.1 + (x₀.2.1 - s.2.1) * d.2.1 +
      (x₀.2.2 - s.2.2) * d.2.2) /
        Real.sqrt ((x₀.1 - s.1) ^ 2 + (x₀.2.1 - s.2.1) ^ 2 +
          (x₀.2.2 - s.2.2) ^ 2) + db := by
  field_simp

end EarthScience
