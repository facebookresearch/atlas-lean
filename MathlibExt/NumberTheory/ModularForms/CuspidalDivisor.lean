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

public import MathlibExt.AlgebraicGeometry.Curve.Divisor
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

namespace ModularCurve

variable {C : Type*}

/-- The degree of a curve divisor: the sum of its coefficients. -/
def divisorDegree (D : CurveDivisor C) : ℤ :=
  D.sum fun _ n => n

theorem divisorDegree_single (P : C) (n : ℤ) :
    divisorDegree (Finsupp.single P n) = n := by
  simp [divisorDegree]

theorem divisorDegree_sub (D E : CurveDivisor C) :
    divisorDegree (D - E) = divisorDegree D - divisorDegree E := by
  classical
  simp [divisorDegree, Finsupp.sum_sub_index]

/-- The cuspidal divisor attached to two cusps: the difference of the
two single-point divisors. -/
noncomputable def cuspidalDivisor (cuspZero cuspInfty : C) : CurveDivisor C :=
  Finsupp.single cuspZero 1 - Finsupp.single cuspInfty 1

theorem cuspidalDivisor_def (cuspZero cuspInfty : C) :
    cuspidalDivisor cuspZero cuspInfty =
      Finsupp.single cuspZero 1 - Finsupp.single cuspInfty 1 :=
  rfl

theorem divisorDegree_cuspidalDivisor (cuspZero cuspInfty : C) :
    divisorDegree (cuspidalDivisor cuspZero cuspInfty) = 0 := by
  rw [cuspidalDivisor_def, divisorDegree_sub, divisorDegree_single,
    divisorDegree_single, sub_self]

theorem cuspidalDivisor_self (P : C) : cuspidalDivisor P P = 0 := by
  simp [cuspidalDivisor_def]

theorem coeff_cuspidalDivisor_self (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    CurveDivisor.coeff (cuspidalDivisor cuspZero cuspInfty) cuspZero = 1 := by
  classical
  simp [cuspidalDivisor_def, CurveDivisor.coeff, Finsupp.single_apply, h]

theorem cuspidalDivisor_ne_zero (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    cuspidalDivisor cuspZero cuspInfty ≠ 0 := by
  intro h0
  have := coeff_cuspidalDivisor_self cuspZero cuspInfty h
  rw [h0] at this
  simp [CurveDivisor.coeff] at this

/-- The cuspidal divisor as a degree-zero divisor. -/
noncomputable def cuspidalDivisorDegZero (cuspZero cuspInfty : C) :
    {D : CurveDivisor C // divisorDegree D = 0} :=
  ⟨cuspidalDivisor cuspZero cuspInfty, divisorDegree_cuspidalDivisor cuspZero cuspInfty⟩

@[simp]
theorem coe_cuspidalDivisorDegZero (cuspZero cuspInfty : C) :
    (cuspidalDivisorDegZero cuspZero cuspInfty : CurveDivisor C) =
      cuspidalDivisor cuspZero cuspInfty :=
  rfl

/-- The divisor class group of a curve with point type `C`, modulo a
chosen subgroup of principal divisors. -/
abbrev DivisorClassGroup (principal : AddSubgroup (CurveDivisor C)) : Type _ :=
  CurveDivisor C ⧸ principal

/-- The cuspidal class: the image of the cuspidal divisor in the divisor
class group modulo principal divisors. -/
noncomputable def cuspidalClass (principal : AddSubgroup (CurveDivisor C))
    (cuspZero cuspInfty : C) : DivisorClassGroup principal :=
  QuotientAddGroup.mk (cuspidalDivisor cuspZero cuspInfty)

theorem cuspidalClass_eq_zero_iff (principal : AddSubgroup (CurveDivisor C))
    (cuspZero cuspInfty : C) :
    cuspidalClass principal cuspZero cuspInfty = 0 ↔
      cuspidalDivisor cuspZero cuspInfty ∈ principal := by
  rw [cuspidalClass, QuotientAddGroup.eq_zero_iff]

theorem cuspidalClass_self (principal : AddSubgroup (CurveDivisor C)) (P : C) :
    cuspidalClass principal P P = 0 := by
  rw [cuspidalClass_eq_zero_iff, cuspidalDivisor_self]
  exact principal.zero_mem

end ModularCurve
