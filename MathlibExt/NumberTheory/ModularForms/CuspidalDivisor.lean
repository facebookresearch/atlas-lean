/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_CuspidalClass.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

@[expose] public section

open AlgebraicCurve

namespace ModularCurve

variable {C : Type*}

/-- The cuspidal divisor attached to two cusps: the difference of the
two single-point divisors. -/
noncomputable def cuspidalDivisor (cuspZero cuspInfty : C) : CurveDivisor C :=
  Finsupp.single cuspZero 1 - Finsupp.single cuspInfty 1

theorem cuspidalDivisor_def (cuspZero cuspInfty : C) :
    cuspidalDivisor cuspZero cuspInfty =
      Finsupp.single cuspZero 1 - Finsupp.single cuspInfty 1 :=
  rfl

theorem cuspidalDivisor_self (P : C) : cuspidalDivisor P P = 0 := by
  simp [cuspidalDivisor_def]

theorem coeff_cuspidalDivisor_self (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    CurveDivisor.coeff (cuspidalDivisor cuspZero cuspInfty) cuspZero = 1 := by
  classical
  simp [cuspidalDivisor_def, CurveDivisor.coeff, h]

theorem cuspidalDivisor_ne_zero (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    cuspidalDivisor cuspZero cuspInfty ≠ 0 := by
  intro h0
  have := coeff_cuspidalDivisor_self cuspZero cuspInfty h
  rw [h0] at this
  simp [CurveDivisor.coeff] at this

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The degree of the cuspidal divisor of two places is the difference of their degrees. -/
theorem degree_cuspidalDivisor (cuspZero cuspInfty : Place K F) :
    Divisor.degree (cuspidalDivisor cuspZero cuspInfty) =
      (cuspZero.deg : ℤ) - cuspInfty.deg := by
  rw [cuspidalDivisor_def, map_sub, Divisor.degree_single, Divisor.degree_single, one_mul,
    one_mul]

/-- The cuspidal divisor of two places has degree zero exactly when the two places have the
same degree. -/
theorem cuspidalDivisor_mem_degZero_iff (cuspZero cuspInfty : Place K F) :
    cuspidalDivisor cuspZero cuspInfty ∈ Divisor.degZero (K := K) (F := F) ↔
      cuspZero.deg = cuspInfty.deg := by
  rw [Divisor.mem_degZero, degree_cuspidalDivisor, sub_eq_zero, Nat.cast_inj]

/-- The cuspidal divisor of two places of the same degree, as a divisor of degree zero. -/
noncomputable def cuspidalDivisorDegZero (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) : Divisor.degZero (K := K) (F := F) :=
  ⟨cuspidalDivisor cuspZero cuspInfty, (cuspidalDivisor_mem_degZero_iff cuspZero cuspInfty).mpr h⟩

@[simp]
theorem coe_cuspidalDivisorDegZero (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) :
    (cuspidalDivisorDegZero cuspZero cuspInfty h : Divisor K F) =
      cuspidalDivisor cuspZero cuspInfty :=
  rfl

/-- The cuspidal class: the class in `Pic0 K F` of the cuspidal divisor of two places of the
same degree. -/
noncomputable def cuspidalClass (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) : Pic0 K F :=
  Pic0.mk (cuspidalDivisorDegZero cuspZero cuspInfty h)

/-- The cuspidal class vanishes exactly when the cuspidal divisor is principal, that is, the
divisor of a nonzero element of `F`. -/
theorem cuspidalClass_eq_zero_iff (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) :
    cuspidalClass cuspZero cuspInfty h = 0 ↔
      Divisor.IsPrincipal (cuspidalDivisor cuspZero cuspInfty) :=
  Pic0.mk_eq_zero_iff _

theorem cuspidalClass_self (P : Place K F) : cuspidalClass P P rfl = 0 := by
  rw [cuspidalClass_eq_zero_iff, cuspidalDivisor_self]
  exact ⟨1, one_ne_zero, fun v => by simp⟩

end ModularCurve
