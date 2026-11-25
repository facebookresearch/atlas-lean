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

/-- Source-shaped consumer: the cuspidal class attached to two cusps, with the original two-cusp
binders, is the `Pic0` class of the degree-zero cuspidal divisor. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (cuspZero cuspInfty : Place K F)
    (h : cuspZero.deg = cuspInfty.deg) :
    cuspidalClass cuspZero cuspInfty h = Pic0.mk (cuspidalDivisorDegZero cuspZero cuspInfty h) :=
  rfl

/-- Higher-universe consumer. -/
example {K : Type 1} {F : Type 2} [Field K] [Field F] [Algebra K F]
    (cuspZero cuspInfty : Place K F) (h : cuspZero.deg = cuspInfty.deg) :
    Divisor.degree (cuspidalDivisor cuspZero cuspInfty) = 0 := by
  rw [degree_cuspidalDivisor, h, sub_self]

/-- The degree weights each place by its degree, so the cuspidal divisor has degree zero exactly
when the two cusps have the same degree. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (cuspZero cuspInfty : Place K F) :
    cuspidalDivisor cuspZero cuspInfty ∈ Divisor.degZero (K := K) (F := F) ↔
      cuspZero.deg = cuspInfty.deg :=
  cuspidalDivisor_mem_degZero_iff cuspZero cuspInfty

/-- Boundary example: when the two cusps coincide, the cuspidal divisor and its class vanish, so
distinctness of the cusps is essential. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) :
    cuspidalDivisor P P = 0 ∧ cuspidalClass P P rfl = 0 :=
  ⟨cuspidalDivisor_self P, cuspidalClass_self P⟩

/-- When the cusps are distinct, the cuspidal divisor itself is nonzero; its class vanishes
exactly when the divisor is the divisor of a nonzero function. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (cuspZero cuspInfty : Place K F)
    (h : cuspZero ≠ cuspInfty) (hdeg : cuspZero.deg = cuspInfty.deg) :
    cuspidalDivisor cuspZero cuspInfty ≠ 0 ∧
      (cuspidalClass cuspZero cuspInfty hdeg = 0 ↔
        ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, cuspidalDivisor cuspZero cuspInfty v = v.ord f) :=
  ⟨cuspidalDivisor_ne_zero cuspZero cuspInfty h, cuspidalClass_eq_zero_iff cuspZero cuspInfty hdeg⟩

/-- A function whose divisor is the cuspidal divisor makes the cuspidal class vanish. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (cuspZero cuspInfty : Place K F)
    (hdeg : cuspZero.deg = cuspInfty.deg) (f : F) (hf : f ≠ 0)
    (hdiv : ∀ v : Place K F, cuspidalDivisor cuspZero cuspInfty v = v.ord f) :
    cuspidalClass cuspZero cuspInfty hdeg = 0 :=
  (cuspidalClass_eq_zero_iff cuspZero cuspInfty hdeg).mpr ⟨f, hf, hdiv⟩

/-- The cuspidal divisor is defined on any type of points. -/
example {C : Type*} (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    CurveDivisor.coeff (cuspidalDivisor cuspZero cuspInfty) cuspZero = 1 :=
  coeff_cuspidalDivisor_self cuspZero cuspInfty h

end CuspidalDivisorTest
