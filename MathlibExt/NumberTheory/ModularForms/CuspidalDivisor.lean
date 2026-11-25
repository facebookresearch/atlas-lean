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

/-!
# The cuspidal divisor and the cuspidal class

The source defines the cuspidal divisor of the modular curve `X₀(N)` over the algebraic closure of
`ℚ` as the difference of its cusps at zero and at infinity, and the cuspidal class as the class of
that divisor in `Pic0`. Neither Mathlib nor this library constructs the function field of `X₀(N)`
or its cusps as places, so the declarations here take the function field `F/K` and the two cusp
places as explicit parameters. They are thin wrappers around `CurveDivisor.pointDiff` and
`AlgebraicCurve.Pic0.mk`: nothing checks that the two places are cusps, and the statements hold
for any two places.
-/

@[expose] public section

open AlgebraicCurve

namespace ModularCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The cuspidal divisor `cuspZero - cuspInfty`. The places `cuspZero` and `cuspInfty` stand for
the cusps at zero and at infinity of a modular curve with function field `F`; they are explicit
parameters because no construction of those cusps is available here, and any two places are
accepted. -/
noncomputable def cuspidalDivisor (cuspZero cuspInfty : Place K F) : Divisor K F :=
  CurveDivisor.pointDiff cuspZero cuspInfty

theorem cuspidalDivisor_def (cuspZero cuspInfty : Place K F) :
    cuspidalDivisor cuspZero cuspInfty = CurveDivisor.pointDiff cuspZero cuspInfty :=
  rfl

variable [∀ v : Place K F, FiniteDimensional K v.ResidueField]

/-- The cuspidal divisor of two cusp places of the same degree, as a divisor of degree zero. -/
noncomputable def cuspidalDivisorDegZero (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) : Divisor.degZero (K := K) (F := F) :=
  ⟨cuspidalDivisor cuspZero cuspInfty,
    (Divisor.pointDiff_mem_degZero_iff cuspZero cuspInfty).mpr h⟩

@[simp]
theorem coe_cuspidalDivisorDegZero (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) :
    (cuspidalDivisorDegZero cuspZero cuspInfty h : Divisor K F) =
      cuspidalDivisor cuspZero cuspInfty :=
  rfl

/-- The cuspidal class: the class in `Pic0 K F` of the cuspidal divisor of two cusp places of the
same degree. As for `cuspidalDivisor`, the cusp places are explicit parameters, and any two places
of the same degree are accepted. -/
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

/-- When the two cusp places coincide, the cuspidal class vanishes. -/
theorem cuspidalClass_self (P : Place K F) : cuspidalClass P P rfl = 0 := by
  rw [cuspidalClass_eq_zero_iff, cuspidalDivisor_def, CurveDivisor.pointDiff_self]
  exact ⟨1, one_ne_zero, fun v => by simp⟩

end ModularCurve
