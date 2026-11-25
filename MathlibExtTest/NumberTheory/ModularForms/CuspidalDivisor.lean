/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspidalDivisor

@[expose] public section

namespace CuspidalDivisorTest

open AlgebraicCurve ModularCurve

/-- The cuspidal divisor is the point difference of the two cusp places it is given. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (cuspZero cuspInfty : Place K F) :
    cuspidalDivisor cuspZero cuspInfty = CurveDivisor.pointDiff cuspZero cuspInfty :=
  rfl

/-- Higher-universe consumer: cusp places of the same degree give a degree-zero divisor. -/
example {K : Type 1} {F : Type 2} [Field K] [Field F] [Algebra K F]
    [∀ v : Place K F, FiniteDimensional K v.ResidueField]
    (cuspZero cuspInfty : Place K F) (h : cuspZero.deg = cuspInfty.deg) :
    Divisor.degree (cuspidalDivisor cuspZero cuspInfty) = 0 := by
  rw [cuspidalDivisor_def, Divisor.degree_pointDiff, h, sub_self]

section Places

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [∀ v : Place K F, FiniteDimensional K v.ResidueField]

/-- Source-shaped consumer: the cuspidal class attached to two cusps, with the original two-cusp
binders, is the `Pic0` class of the degree-zero cuspidal divisor. -/
example (cuspZero cuspInfty : Place K F) (h : cuspZero.deg = cuspInfty.deg) :
    cuspidalClass cuspZero cuspInfty h = Pic0.mk (cuspidalDivisorDegZero cuspZero cuspInfty h) :=
  rfl

/-- Boundary example: when the two cusp places coincide, the cuspidal divisor and its class
vanish, so distinctness of the cusps is essential. -/
example (P : Place K F) : cuspidalDivisor P P = 0 ∧ cuspidalClass P P rfl = 0 :=
  ⟨CurveDivisor.pointDiff_self P, cuspidalClass_self P⟩

/-- When the cusp places are distinct, the cuspidal divisor itself is nonzero; its class vanishes
exactly when the divisor is the divisor of a nonzero function. -/
example (cuspZero cuspInfty : Place K F) (h : cuspZero ≠ cuspInfty)
    (hdeg : cuspZero.deg = cuspInfty.deg) :
    cuspidalDivisor cuspZero cuspInfty ≠ 0 ∧
      (cuspidalClass cuspZero cuspInfty hdeg = 0 ↔
        ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, cuspidalDivisor cuspZero cuspInfty v = v.ord f) :=
  ⟨CurveDivisor.pointDiff_ne_zero cuspZero cuspInfty h,
    cuspidalClass_eq_zero_iff cuspZero cuspInfty hdeg⟩

/-- A function whose divisor is the cuspidal divisor makes the cuspidal class vanish. -/
example (cuspZero cuspInfty : Place K F) (hdeg : cuspZero.deg = cuspInfty.deg) (f : F)
    (hf : f ≠ 0) (hdiv : ∀ v : Place K F, cuspidalDivisor cuspZero cuspInfty v = v.ord f) :
    cuspidalClass cuspZero cuspInfty hdeg = 0 :=
  (cuspidalClass_eq_zero_iff cuspZero cuspInfty hdeg).mpr ⟨f, hf, hdiv⟩

end Places

end CuspidalDivisorTest
