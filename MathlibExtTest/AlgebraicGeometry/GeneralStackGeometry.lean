/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
import Mathlib.CategoryTheory.SingleObj

/-! # Actual 2-fibre and isomorphism-value checks

The pointwise 2-fibre of two points in the one-object groupoid of Z
retains a different object for each comparison automorphism.
Equal first and second projections do not
identify different comparisons. This probes the data lost by replacing
a 2-fibre product with an ordinary product of point sets.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.GeneralStackGeometry

open CategoryTheory _root_.AlgebraicGeometry.GeneralStackGeometry

abbrev G := Multiplicative ℤ

def pointFunctor : Discrete PUnit ⥤ SingleObj G :=
  (Functor.const (Discrete PUnit)).obj (SingleObj.star G)

def comparisonPoint (n : ℤ) : IsoFibre pointFunctor pointFunctor :=
  ⟨⟨Discrete.mk PUnit.unit, Discrete.mk PUnit.unit, Multiplicative.ofAdd n⟩,
    by
      change IsIso (C := SingleObj G) (X := SingleObj.star G) (Y := SingleObj.star G)
        (Multiplicative.ofAdd n)
      refine ⟨⟨Multiplicative.ofAdd (-n), ?_, ?_⟩⟩
      · change -n + n = 0
        exact neg_add_cancel n
      · change n + -n = 0
        exact add_neg_cancel n⟩

example : IsGroupoid (IsoFibre pointFunctor pointFunctor) := inferInstance

example : (isoFibreFst pointFunctor pointFunctor).obj (comparisonPoint 0) =
    (isoFibreFst pointFunctor pointFunctor).obj (comparisonPoint 1) := rfl

example : (isoFibreSnd pointFunctor pointFunctor).obj (comparisonPoint 0) =
    (isoFibreSnd pointFunctor pointFunctor).obj (comparisonPoint 1) := rfl

example : (isoFibreComparison pointFunctor pointFunctor).hom.app (comparisonPoint 1) =
    Multiplicative.ofAdd (1 : ℤ) := rfl

example : ¬ Nonempty (comparisonPoint 0 ⟶ comparisonPoint 1) := by
  rintro ⟨h⟩
  have hc := h.hom.w
  change Multiplicative.ofAdd (1 : ℤ) * 1 = 1 * Multiplicative.ofAdd (0 : ℤ) at hc
  simp only [mul_one, one_mul] at hc
  have heq : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd hc
  exact Int.one_ne_zero heq

universe u

example (X : AlgebraicGeometry.FppfStacks.StackInGroupoids.{u})
    {T : AlgebraicGeometry.Scheme.{u}} (x y : Fibre X T) (V : Over T)
    (e : ULift.{u + 1} ((reindex X V.hom).obj x ≅ (reindex X V.hom).obj y)) :
    ((isomPresheafObjEquiv X x y V) e).down = e.down.hom := rfl

example (S : AlgebraicGeometry.Scheme.{u})
    (F : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1})
    (groupoids : ∀ T : Over S, IsGroupoid (F.obj (.mk (Opposite.op T))))
    (stack : F.IsStack (AlgebraicGeometry.Scheme.fppfTopology.over S)) :
    (RelativeStack.of S F groupoids stack).toPseudofunctor = F := rfl

example {S : AlgebraicGeometry.Scheme.{u}} (T : Over S)
    (A : AlgebraicSpaceOver T.left) (V : Over T) :
    (relativeSpacePresheaf T A).obj (Opposite.op V) =
      {x : A.sheaf.obj.obj (Opposite.op V.left.left) //
        A.structural.hom.app (Opposite.op V.left.left) x = ULift.up V.hom.left} := rfl

example {S : AlgebraicGeometry.Scheme.{u}} (X : RelativeStack S)
    {U T : Over S} (x : X.Fibre U) (y : X.Fibre T) (V : Over T)
    (z : (pointComparisonPresheaf X.toPseudofunctor x y).obj (Opposite.op V)) :
    z.1.left ≫ U.hom = V.left.hom := Over.w z.1

end MathlibExtTest.AlgebraicGeometry.GeneralStackGeometry
