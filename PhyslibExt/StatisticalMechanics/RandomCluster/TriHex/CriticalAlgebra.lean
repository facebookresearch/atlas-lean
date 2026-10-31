/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Critical polynomials of the homogeneous triangular and hexagonal random-cluster models

The cubic equations for the self-dual (critical) edge odds of the FK model on the triangular and
hexagonal lattices, and their exchange under planar duality `y * y* = q`.

## i. Overview

For the random-cluster model with cluster weight `q` and edge odds `y = p / (1 - p)`, the critical
point of the homogeneous triangular lattice is the positive root of `y ^ 3 + 3 y ^ 2 - q = 0`
(`triangularFKCriticalPolynomial`), and that of the hexagonal lattice is the positive root of
`y ^ 3 - 3 q y - q ^ 2 = 0` (`hexagonalFKCriticalPolynomial`). This file proves the purely
algebraic fact that these two cubics are exchanged by the duality relation `y * y* = q`: if `y`
solves the triangular equation then `y* = q / y` solves the hexagonal one and conversely. All
statements are unconditional identities over `ℝ` (with the stated nonvanishing hypotheses); they
do not assert that either root is the critical point of an FK measure.

## ii. Key results

- `triangularFKCritical_iff_hexagonal_of_dual` : under `y * y* = q` (with `y, y* ≠ 0`), `y` is a
  triangular critical root iff `y*` is a hexagonal critical root. Unconditional.
- `hexagonalFKCritical_div_of_triangular` : the dual odds `q / y` of a triangular root is a
  hexagonal root. Unconditional.

## iii. Table of contents

- A. The critical polynomials
- B. Duality between the two cubics

## iv. References

- R. J. Baxter, H. N. V. Temperley and S. E. Ashley, *Triangular Potts model at its transition
  temperature, and related models*, Proc. R. Soc. Lond. A 358 (1978) 535–559.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
-/

@[expose] public section

namespace StatMech.FK.TriHex

/-! ## A. The critical polynomials -/

/-- The triangular-lattice FK critical polynomial `y ^ 3 + 3 y ^ 2 - q` in the edge odds `y = p / (1
- p)`; its positive root is the critical odds of the homogeneous triangular random-cluster model
with cluster weight `q` (Grimmett, §6.6). -/
def triangularFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 + 3 * y ^ 2 - q

/-- The hexagonal-lattice FK critical polynomial `y ^ 3 - 3 q y - q ^ 2` in the edge odds `y = p /
(1 - p)`; its positive root is the critical odds of the homogeneous hexagonal random-cluster model
with cluster weight `q` (Grimmett, §6.6). -/
def hexagonalFKCriticalPolynomial (q y : ℝ) : ℝ :=
  y ^ 3 - 3 * q * y - q ^ 2

/-! ## B. Duality between the two cubics -/

lemma dualOdds_eq_of_triangularFKCritical {q y yStar : ℝ}
    (hy : y ≠ 0) (hdual : y * yStar = q)
    (htri : triangularFKCriticalPolynomial q y = 0) :
    yStar = y ^ 2 + 3 * y := by
  unfold triangularFKCriticalPolynomial at htri
  rw [← hdual] at htri
  apply (mul_left_cancel₀ hy)
  nlinarith

lemma hexagonalFKCritical_of_dual_triangular {q y yStar : ℝ}
    (hy : y ≠ 0) (hdual : y * yStar = q)
    (htri : triangularFKCriticalPolynomial q y = 0) :
    hexagonalFKCriticalPolynomial q yStar = 0 := by
  have hStar := dualOdds_eq_of_triangularFKCritical hy hdual htri
  unfold hexagonalFKCriticalPolynomial
  rw [← hdual, hStar]
  ring

lemma hexagonalFKCritical_div_of_triangular {q y : ℝ}
    (hy : y ≠ 0) (htri : triangularFKCriticalPolynomial q y = 0) :
    hexagonalFKCriticalPolynomial q (q / y) = 0 := by
  apply hexagonalFKCritical_of_dual_triangular hy
  · field_simp
  · exact htri

lemma triangularFKCritical_of_dual_hexagonal {q y yStar : ℝ}
    (hyStar : yStar ≠ 0) (hdual : y * yStar = q)
    (hhex : hexagonalFKCriticalPolynomial q yStar = 0) :
    triangularFKCriticalPolynomial q y = 0 := by
  unfold hexagonalFKCriticalPolynomial at hhex
  rw [← hdual] at hhex
  have hStar : yStar = y ^ 2 + 3 * y := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hyStar))
    nlinarith
  unfold triangularFKCriticalPolynomial
  rw [← hdual, hStar]
  ring

/-- Triangular–hexagonal duality of the homogeneous FK critical points: when `y * y* = q`, the odds
`y` solves the triangular critical cubic iff the dual odds `y*` solves the hexagonal one (Grimmett,
*The Random-Cluster Model*, §6.6). -/
theorem triangularFKCritical_iff_hexagonal_of_dual {q y yStar : ℝ}
    (hy : y ≠ 0) (hyStar : yStar ≠ 0) (hdual : y * yStar = q) :
    triangularFKCriticalPolynomial q y = 0 ↔
      hexagonalFKCriticalPolynomial q yStar = 0 :=
  ⟨hexagonalFKCritical_of_dual_triangular hy hdual,
    triangularFKCritical_of_dual_hexagonal hyStar hdual⟩

end StatMech.FK.TriHex
