/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.SimplicialObject.LatchingEvaluation
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.ComposableArrows.Basic

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite
open scoped Simplicial

universe v₁ v₂ u₁ u₂ u

namespace LatchingEvaluationTest

section Generic

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasPushouts C]

-- Evaluation is literally the generic coefficient comparison, so consumers can mix both APIs.
example (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C] :
    relativeLatchingMapEvaluationIso j k =
      coefficientRelativeLatchingArrowIso ((evaluation J C).obj j) k :=
  relativeLatchingMapEvaluationIso_eq_coefficient j k

-- These public consumers require only the actual shaped colimits and pushouts.
example (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C] :
    relativeLatchingMapArrowFunctor (C := J ⥤ C) k ⋙
        ((evaluation J C).obj j).mapArrow ≅
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).obj
        ((evaluation J C).obj j)).mapArrow ⋙ relativeLatchingMapArrowFunctor (C := C) k :=
  relativeLatchingMapEvaluationIso j k

example (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C]
    {f g : Arrow (SimplicialObject (J ⥤ C))} (q : f ⟶ g) :
    ((relativeLatchingMapArrowFunctor k ⋙ ((evaluation J C).obj j).mapArrow).map q) ≫
        (relativeLatchingMapEvaluationIso j k).hom.app g =
      (relativeLatchingMapEvaluationIso j k).hom.app f ≫
        ((((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).obj
          ((evaluation J C).obj j)).mapArrow ⋙ relativeLatchingMapArrowFunctor k).map q) :=
  (relativeLatchingMapEvaluationIso j k).hom.naturality q

example (j : J) (k : ℕ) [HasColimitsOfShape (latchingIndex k) C]
    {f g : Arrow (SimplicialObject (J ⥤ C))} (q : f ⟶ g) :
    ((((Functor.whiskeringRight SimplexCategoryᵒᵖ (J ⥤ C) C).obj
          ((evaluation J C).obj j)).mapArrow ⋙ relativeLatchingMapArrowFunctor k).map q) ≫
        (relativeLatchingMapEvaluationIso j k).inv.app g =
      (relativeLatchingMapEvaluationIso j k).inv.app f ≫
        ((relativeLatchingMapArrowFunctor k ⋙ ((evaluation J C).obj j).mapArrow).map q) :=
  (relativeLatchingMapEvaluationIso j k).inv.naturality q

end Generic

-- Fin 2 with its preorder category is the walking arrow. The two coefficients
-- are distinct standard simplices, rather than a constant coefficient diagram.
private def simplexStep (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.δ (Fin.last (n + 1))

private def coefficients (n : ℕ) : Fin 2 ⥤ SSet.{u} :=
  ComposableArrows.mk₁ (simplexStep n)

private def coefficientStep (n : ℕ) : coefficients.{u} n ⟶ coefficients (n + 1) :=
  ComposableArrows.homMk₁ (simplexStep n) (simplexStep (n + 1)) (by rfl)

private def diagram (n : ℕ) : SimplicialObject (Fin 2 ⥤ Type u) :=
  (flipFunctor (Fin 2) SimplexCategoryᵒᵖ (Type u)).obj (coefficients n)

private def diagramStep (n : ℕ) : diagram.{u} n ⟶ diagram (n + 1) :=
  (flipFunctor (Fin 2) SimplexCategoryᵒᵖ (Type u)).map (coefficientStep n)

private def square : Arrow.mk (diagramStep.{u} 0) ⟶ Arrow.mk (diagramStep 1) :=
  Arrow.homMk (diagramStep 0) (diagramStep 1) (by rfl)

-- Both endpoint maps change in this concrete whole-arrow square.
example (j : Fin 2) (k : ℕ) :
    ((relativeLatchingMapArrowFunctor k ⋙ ((evaluation (Fin 2) (Type u)).obj j).mapArrow).map
      square) ≫ (relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk (diagramStep 1)) =
      (relativeLatchingMapEvaluationIso j k).hom.app (Arrow.mk (diagramStep 0)) ≫
        ((((Functor.whiskeringRight SimplexCategoryᵒᵖ (Fin 2 ⥤ Type u) (Type u)).obj
          ((evaluation (Fin 2) (Type u)).obj j)).mapArrow ⋙ relativeLatchingMapArrowFunctor k).map
            square) :=
  (relativeLatchingMapEvaluationIso j k).hom.naturality square

-- Zero retains the original chosen initial latching object and evaluated target.
example (j : Fin 2) :
    ((relativeLatchingMapEvaluationIso j 0).hom.app (Arrow.mk (diagramStep.{u} 0))).right =
      𝟙 (((diagram.{u} 1).obj (op ⦋0⦌)).obj j) :=
  relativeLatchingMapEvaluationIso_hom_right j 0 _

-- At degree two both original pushout injections are independently checked.
example (j : Fin 2) :
    (pushout.inl (latchingMap (diagram.{u} 0) 2)
        ((latchingObjectFunctor 2).map (diagramStep 0))).app j ≫
          ((relativeLatchingMapEvaluationIso j 2).hom.app (Arrow.mk (diagramStep 0))).left =
      pushout.inl (latchingMap (diagram 0 ⋙ (evaluation (Fin 2) (Type u)).obj j) 2)
        ((latchingObjectFunctor 2).map
          (Functor.whiskerRight (diagramStep 0) ((evaluation (Fin 2) (Type u)).obj j))) :=
  relativeLatchingMapEvaluationIso_hom_left_inl j 2 _

example (j : Fin 2) :
    (pushout.inr (latchingMap (diagram.{u} 0) 2)
        ((latchingObjectFunctor 2).map (diagramStep 0))).app j ≫
          ((relativeLatchingMapEvaluationIso j 2).hom.app (Arrow.mk (diagramStep 0))).left =
      (colimitObjIsoColimitCompEvaluation (latchingDiagram (diagram.{u} 1) 2) j).hom ≫
        pushout.inr (latchingMap (diagram 0 ⋙ (evaluation (Fin 2) (Type u)).obj j) 2)
          ((latchingObjectFunctor 2).map
            (Functor.whiskerRight (diagramStep 0) ((evaluation (Fin 2) (Type u)).obj j))) :=
  relativeLatchingMapEvaluationIso_hom_left_inr j 2 _

-- The index map is the nonidentity 0→1 of the walking arrow.
example (k : ℕ) :
    ((Functor.mapArrowFunctor (Fin 2 ⥤ Type u) (Type u)).map
        ((evaluation (Fin 2) (Type u)).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))).app
          ((relativeLatchingMapArrowFunctor k).obj (Arrow.mk (diagramStep 0))) ≫
        (relativeLatchingMapEvaluationIso (1 : Fin 2) k).hom.app (Arrow.mk (diagramStep 0)) =
      (relativeLatchingMapEvaluationIso (0 : Fin 2) k).hom.app (Arrow.mk (diagramStep 0)) ≫
        (relativeLatchingMapArrowFunctor (C := Type u) k).map
          (((Functor.mapArrowFunctor (SimplicialObject (Fin 2 ⥤ Type u))
              (SimplicialObject (Type u))).map
            ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Fin 2 ⥤ Type u) (Type u)).map
              ((evaluation (Fin 2) (Type u)).map
                (homOfLE (show (0 : Fin 2) ≤ 1 by decide))))).app (Arrow.mk (diagramStep 0))) :=
  relativeLatchingMapEvaluationIso_hom_index _ k _

-- The coefficient index universe may be larger than the value-category universe.
example (j : Type u₁) (k : ℕ) :
    relativeLatchingMapArrowFunctor (C := Type u₁ ⥤ Type u₂) k ⋙
        ((evaluation (Type u₁) (Type u₂)).obj j).mapArrow ≅
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u₁ ⥤ Type u₂) (Type u₂)).obj
        ((evaluation (Type u₁) (Type u₂)).obj j)).mapArrow ⋙
          relativeLatchingMapArrowFunctor (C := Type u₂) k :=
  relativeLatchingMapEvaluationIso j k

end LatchingEvaluationTest
