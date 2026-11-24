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

open ModularCurve

/-- Source-shaped consumer: the cuspidal class attached to two cusps,
with the original two-cusp binders. -/
example {C : Type*} (principal : AddSubgroup (CurveDivisor C))
    (cuspZero cuspInfty : C) :
    cuspidalClass principal cuspZero cuspInfty =
      QuotientAddGroup.mk (cuspidalDivisor cuspZero cuspInfty) :=
  rfl

/-- Higher-universe consumer. -/
example {C : Type 1} (principal : AddSubgroup (CurveDivisor C))
    (cuspZero cuspInfty : C) :
    divisorDegree (cuspidalDivisor cuspZero cuspInfty) = 0 :=
  divisorDegree_cuspidalDivisor cuspZero cuspInfty

/-- The cuspidal divisor has degree zero for any two cusps. -/
example {C : Type*} (cuspZero cuspInfty : C) :
    divisorDegree (cuspidalDivisor cuspZero cuspInfty) = 0 :=
  divisorDegree_cuspidalDivisor cuspZero cuspInfty

/-- Boundary example: when the two cusps coincide, the cuspidal divisor
and its class vanish, so distinctness of the cusps is essential. -/
example {C : Type*} (principal : AddSubgroup (CurveDivisor C)) (P : C) :
    cuspidalClass principal P P = 0 :=
  cuspidalClass_self principal P

/-- When the cusps are distinct, the cuspidal divisor itself is nonzero;
its class vanishes exactly when it is principal. -/
example {C : Type*} (principal : AddSubgroup (CurveDivisor C))
    (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    cuspidalDivisor cuspZero cuspInfty ≠ 0 ∧
      (cuspidalClass principal cuspZero cuspInfty = 0 ↔
        cuspidalDivisor cuspZero cuspInfty ∈ principal) :=
  ⟨cuspidalDivisor_ne_zero cuspZero cuspInfty h,
    cuspidalClass_eq_zero_iff principal cuspZero cuspInfty⟩

end CuspidalDivisorTest
