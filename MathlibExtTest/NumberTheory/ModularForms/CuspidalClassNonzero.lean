/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspidalClassNonzero

@[expose] public section

namespace CuspidalClassNonzeroTest

open ModularCurve

/-- Source-shaped consumer with the original two-cusp binders. -/
example {C : Type*} (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    cuspidalClass (⊥ : AddSubgroup (CurveDivisor C)) cuspZero cuspInfty ≠ 0 :=
  cuspidalClass_bot_ne_zero cuspZero cuspInfty h

/-- Higher-universe consumer. -/
example {C : Type 1} (cuspZero cuspInfty : C) (h : cuspZero ≠ cuspInfty) :
    cuspidalClass (⊥ : AddSubgroup (CurveDivisor C)) cuspZero cuspInfty ≠ 0 :=
  cuspidalClass_bot_ne_zero cuspZero cuspInfty h

/-- Boundary example: when the cusps coincide, the class is zero, so
distinctness is essential for non-vanishing. -/
example {C : Type*} (P : C) :
    cuspidalClass (⊥ : AddSubgroup (CurveDivisor C)) P P = 0 :=
  cuspidalClass_self ⊥ P

end CuspidalClassNonzeroTest
