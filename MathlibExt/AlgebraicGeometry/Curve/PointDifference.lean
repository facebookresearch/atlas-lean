/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
and
`Definitions/Def_ModularCurve_CuspidalClass.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.Divisor
public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial

/-!
# Point differences on a curve

This file defines the divisor `P - Q` of two points on any type of points. For the places of a
field extension `F/K`, it computes the degree of `P - Q`, and it adds two facts about the group
`AlgebraicCurve.Pic0` of degree-zero divisor classes from `Curve/LPolynomial.lean`: the class of
a divisor of degree zero vanishes exactly when the divisor is principal, and the class of the zero
divisor is zero.

Degrees are those of `Curve/LPolynomial.lean`: `AlgebraicCurve.Place.deg` is the dimension of the
residue field over `K` as a `Module.finrank`, so it is meaningful when the residue field is
finite-dimensional, as it is at every place under `AlgebraicCurve.IsCurveOver`. In that case
`Place.deg_pos` shows that the degree is positive.
-/

@[expose] public section

namespace CurveDivisor

variable {C : Type*}

/-- The divisor `P - Q` of two points `P` and `Q`: the difference of the two single-point
divisors. -/
noncomputable def pointDiff (P Q : C) : CurveDivisor C :=
  Finsupp.single P 1 - Finsupp.single Q 1

theorem pointDiff_def (P Q : C) : pointDiff P Q = Finsupp.single P 1 - Finsupp.single Q 1 :=
  rfl

theorem pointDiff_self (P : C) : pointDiff P P = 0 := by
  simp [pointDiff_def]

/-- For distinct points `P` and `Q`, the divisor `P - Q` has coefficient `1` at `P`. -/
theorem coeff_pointDiff_left (P Q : C) (h : P ≠ Q) : coeff (pointDiff P Q) P = 1 := by
  classical
  simp [pointDiff_def, coeff, h]

theorem pointDiff_ne_zero (P Q : C) (h : P ≠ Q) : pointDiff P Q ≠ 0 := by
  intro h0
  have := coeff_pointDiff_left P Q h
  rw [h0] at this
  simp [coeff] at this

end CurveDivisor

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- The degree of a place whose residue field is finite-dimensional over `K` is positive. -/
theorem deg_pos [Module.Finite K v.ResidueField] : 0 < v.deg :=
  Module.finrank_pos

end Place

namespace Divisor

/-- The degree of the divisor `P - Q` of two places is the difference of their degrees. -/
theorem degree_pointDiff (P Q : Place K F) :
    degree (CurveDivisor.pointDiff P Q) = (P.deg : ℤ) - Q.deg := by
  rw [CurveDivisor.pointDiff_def, map_sub, degree_single, degree_single, one_mul, one_mul]

/-- The divisor `P - Q` of two places has degree zero exactly when the two places have the same
degree. -/
theorem pointDiff_mem_degZero_iff (P Q : Place K F) :
    CurveDivisor.pointDiff P Q ∈ degZero (K := K) (F := F) ↔ P.deg = Q.deg := by
  rw [mem_degZero, degree_pointDiff, sub_eq_zero, Nat.cast_inj]

end Divisor

namespace Pic0

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 :=
  rfl

/-- The class of a divisor of degree zero vanishes exactly when the divisor is principal. -/
theorem mk_eq_zero_iff (D : Divisor.degZero (K := K) (F := F)) :
    mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

end Pic0

end AlgebraicCurve
