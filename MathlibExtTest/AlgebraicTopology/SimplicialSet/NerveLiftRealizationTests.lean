/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization

noncomputable section

open CategoryTheory

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (E : C ≌ D)

example : ContinuousMap.HomotopyEquiv (SSet.toTop.obj (nerve C))
    (SSet.toTop.obj (nerve D)) :=
  CategoryTheory.realizedNerveEquivalence E

example (c : C) :
    (CategoryTheory.realizedNerveEquivalence E).toFun
      (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        SSet.realizedVertex (ComposableArrows.mk₀ (E.functor.obj c)) :=
  CategoryTheory.realizedNerveEquivalence_vertex E c

example (d : D) :
    (CategoryTheory.realizedNerveEquivalence E).invFun
      (SSet.realizedVertex (ComposableArrows.mk₀ d)) =
        SSet.realizedVertex (ComposableArrows.mk₀ (E.inverse.obj d)) :=
  CategoryTheory.realizedNerveEquivalence_inv_vertex E d

example : Nonempty (ContinuousMap.Homotopy
    ((CategoryTheory.realizedNerveEquivalence E).invFun.comp
      (CategoryTheory.realizedNerveEquivalence E).toFun)
    (ContinuousMap.id (SSet.toTop.obj (nerve C)))) :=
  (CategoryTheory.realizedNerveEquivalence E).left_inv

example : Nonempty (ContinuousMap.Homotopy
    ((CategoryTheory.realizedNerveEquivalence E).toFun.comp
      (CategoryTheory.realizedNerveEquivalence E).invFun)
    (ContinuousMap.id (SSet.toTop.obj (nerve D)))) :=
  (CategoryTheory.realizedNerveEquivalence E).right_inv

end
