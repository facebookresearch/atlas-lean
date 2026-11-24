/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.WeilReciprocity
public import MathlibExt.AlgebraicGeometry.Curve.RationalWeilReciprocity

@[expose] public section

open AlgebraicCurve

-- `exactSource` consumer with the original binders.
example (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] : WeilReciprocity K F :=
  AlgebraicCurve.weilReciprocity K F

-- The statement is universe polymorphic: `K` and `F` may live in different universes.
universe u v in
example (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F :=
  AlgebraicCurve.weilReciprocity K F

-- A concrete instance: the rational function field itself, whose principal divisors are
-- supplied by `RationalFunctionField.hasPrincipalDivisors`.
example (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : WeilReciprocity K (RatFunc K) :=
  haveI := RationalFunctionField.hasPrincipalDivisors K
  AlgebraicCurve.weilReciprocity K (RatFunc K)

-- The same conclusion from the rational-function-field case directly.
example (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : WeilReciprocity K (RatFunc K) :=
  RationalFunctionField.weilReciprocity K

-- Unfolded form: for nonzero `f, g` with disjoint divisors on rational places,
-- `f(div g) = g(div f)`.
example (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] (f g : F) (Df Dg : Divisor K F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hDf : ∀ v : Place K F, Df v = v.ord f) (hDg : ∀ v : Place K F, Dg v = v.ord g)
    (hdisj : ∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) :
    Divisor.evalFun f Dg = Divisor.evalFun g Df :=
  AlgebraicCurve.weilReciprocity K F f g Df Dg hf hg hDf hDg hdisj
    (fun v _ => Place.isRational_of_isAlgClosed v) (fun v _ => Place.isRational_of_isAlgClosed v)

-- Boundary: evaluation on the zero divisor is `1`, so for a constant `g` (whose divisor is
-- zero) the reciprocity law says `g(div f) = 1`.
example (K F : Type*) [Field K] [Field F] [Algebra K F] (f : F) :
    Divisor.evalFun f (0 : Divisor K F) = 1 :=
  Divisor.evalFun_zero f
