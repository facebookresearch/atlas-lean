/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.WeilReciprocity
public import MathlibExt.AlgebraicGeometry.Curve.RationalWeilReciprocity
import MathlibExt.AlgebraicGeometry.Curve.NormFormula

@[expose] public section

open AlgebraicCurve Polynomial

-- `exactSource` consumer with the original binders, including the principal-divisor hypothesis
-- of the source, which the theorem no longer needs.
example (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] : WeilReciprocity K F :=
  AlgebraicCurve.weilReciprocity K F

-- No principal-divisor hypothesis on `F`. The statement is universe polymorphic.
universe u v in
example (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] : WeilReciprocity K F :=
  AlgebraicCurve.weilReciprocity K F

-- A concrete instance: the rational function field itself.
example (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] : WeilReciprocity K (RatFunc K) :=
  AlgebraicCurve.weilReciprocity K (RatFunc K)

-- The same conclusion from the rational-function-field case, in any characteristic.
example (K : Type*) [Field K] [IsAlgClosed K] : WeilReciprocity K (RatFunc K) :=
  RationalFunctionField.weilReciprocity K

-- Unfolded form: for nonzero `f, g` with disjoint divisors, `f(div g) = g(div f)`; every place
-- is rational.
example (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    (f g : F) (Df Dg : Divisor K F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hDf : ∀ v : Place K F, Df v = v.ord f) (hDg : ∀ v : Place K F, Dg v = v.ord g)
    (hdisj : ∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) :
    CurveDivisor.evalFun f Dg (fun v _ => Place.isRational_of_isAlgClosed_of_finiteDimensional v)
      = CurveDivisor.evalFun g Df
          (fun v _ => Place.isRational_of_isAlgClosed_of_finiteDimensional v) :=
  AlgebraicCurve.weilReciprocity K F f g Df Dg hf hg hDf hDg hdisj _ _

-- The constant case: principal divisors of finite extensions of `RatFunc K` have degree zero.
example (K F : Type*) [Field K] [CharZero K] [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] (f : F) (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = v.ord f) : Divisor.degree D = 0 :=
  Divisor.degree_eq_zero_of_forall_eq_ord D hD

section Extension

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

-- The pullback weights each place above `v` by its ramification index; it needs no principal
-- divisors on `F'`, and agrees with `Divisor.pullback` when they exist.
example (D : Divisor K F) (w : Place K F') :
    Divisor.pullbackOver F' D w = w.ramificationIndex F * D (w.restrict F) :=
  Divisor.pullbackOver_apply D w

example [HasPrincipalDivisors K F'] (D : Divisor K F) :
    Divisor.pullback F' D = Divisor.pullbackOver F' D :=
  Divisor.pullback_eq_pullbackOver D

-- The divisor of `algebraMap F F' g` is the pullback of the divisor of `g`.
example {g : F} {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) (w : Place K F') :
    Divisor.pullbackOver F' D w = w.ord (algebraMap F F' g) :=
  Divisor.pullbackOver_apply_eq_ord hD w

-- The order of a norm: inertia degrees weight the orders of `f` above `v`.
example [CharZero F] (v : Place K F) {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f :=
  Place.ord_norm_eq_sum_fiber v hf

-- The value of a norm: ramification indices weight the values of `f` above `v`, at rational
-- places where `f` is a unit.
example (v : Place K F) (f : F') (hf : f ≠ 0) (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiberOver F', w.IsRational) (hord : ∀ w ∈ v.fiberOver F', w.ord f = 0) :
    v.evalAt hv (Algebra.norm F f) = ∏ w ∈ (v.fiberOver F').attach,
      (w : Place K F').evalAt (hrat w w.2) f ^ (w : Place K F').ramificationIndex F :=
  Place.evalAt_norm_eq_prod_fiber v f hf hv hrat hord

-- The pushforward of the divisor of `f` is the divisor of its norm.
example [CharZero F] {f : F'} (hf : f ≠ 0) {D : Divisor K F'} (hD : ∀ w, D w = w.ord f)
    {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) :
    Divisor.pushforward F D = E :=
  Divisor.pushforward_div hf hD hE

end Extension

section RationalFunctionField

open RationalFunctionField

variable (K : Type*) [Field K]

-- Values at the place of a point: a polynomial evaluates to its value at the point.
example (a : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
        (algebraMap K[X] (RatFunc K) (X ^ 2 + C 1)) = a ^ 2 + 1 := by
  rw [evalAt_placeOfPoint_algebraMap]
  simp

example (a b : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
        (algebraMap K[X] (RatFunc K) (X - C b)) = a - b :=
  evalAt_placeOfPoint_X_sub_C a b

-- The value at infinity of `(X - a) / (X - a₀)` is `1`.
example [DecidableEq (RatFunc K)] (a a₀ : K) :
    (placeInfty K).evalAt (isRational_placeInfty K)
        (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀)) = 1 :=
  evalAt_placeInfty_X_sub_C_div a a₀

-- A pole: `X` has a pole at infinity, so its value there is `0`.
example [DecidableEq (RatFunc K)] :
    (placeInfty K).evalAt (isRational_placeInfty K) (algebraMap K[X] (RatFunc K) X) = 0 := by
  have hX : algebraMap K[X] (RatFunc K) X ∉ (placeInfty K).toValuationSubring := fun h => by
    have := (placeInfty K).ord_nonneg_of_mem h
    rw [ord_placeInfty_algebraMap X_ne_zero, natDegree_X] at this
    omega
  rw [Place.evalAt, dite_eq_right hX]

-- The divisor of `X - b` is `[b] - [∞]`.
example [DecidableEq (RatFunc K)] (b : K) :
    principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b))
      = Finsupp.single (placeOfPoint K b) 1 + Finsupp.single (placeInfty K) (-1) :=
  principalDivisor_X_sub_C b

example [DecidableEq (RatFunc K)] (b : K) :
    principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)) (placeInfty K) = -1 := by
  rw [principalDivisor_X_sub_C, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (placeOfPoint_ne_placeInfty K b).symm, Finsupp.single_eq_same,
    zero_add]

-- Principal divisors of `RatFunc K` have degree zero in every characteristic.
example (f : RatFunc K) (D : Divisor K (RatFunc K)) (hD : ∀ v, D v = v.ord f) :
    Divisor.degree D = 0 :=
  RationalFunctionField.degree_eq_zero_of_forall_eq_ord D hD

end RationalFunctionField

-- Boundary: evaluation on the zero divisor is `1`, so for a constant `g` (whose divisor is
-- zero) the reciprocity law says `g(div f) = 1`.
example (K F : Type*) [Field K] [Field F] [Algebra K F] (f : F) :
    CurveDivisor.evalFun f (0 : Divisor K F) (by simp) = 1 :=
  CurveDivisor.evalFun_zero f _
