/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap

/-!
# Actual composition of original realized functor maps in independent worlds

Each SAME original map has its proved larger-envelope recipe. Use a common
working envelope for both original maps, with their original up/down
category equivalences and lift homeomorphisms. The intermediate chart
roundtrip and actual nerve functor composition give whole map composition.
The original maps, spaces and all six category universe roles are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uA vA uB vB uE vE

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B] {E : Type uE} [Category.{vE} E]

private theorem actualIndependentWorldMapComposition (F : A ⥤ B) (G : B ⥤ E) :
    realizedNerveFunctorMap (F ⋙ G) =
      (realizedNerveFunctorMap G).comp (realizedNerveFunctorMap F) := by
  rw [realizedNerveFunctorMap_larger_recipe.{uA, vA, uE, vE, max uA vA uB vB uE vE} (F ⋙ G),
    realizedNerveFunctorMap_larger_recipe.{uA, vA, uB, vB, max uA vA uB vB uE vE} F,
    realizedNerveFunctorMap_larger_recipe.{uB, vB, uE, vE, max uA vA uB vB uE vE} G]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB uE vE} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB uE vE} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uA vA uB vB uE vE} E
  let UA := ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
    max uA vA uB vB uE vE, vA, uA} A
  let UB := ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
    max uA vA uB vB uE vE, vB, uB} B
  let UE := ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
    max uA vA uB vB uE vE, vE, uE} E
  let LF := UA.inverse ⋙ F ⋙ UB.functor
  let LG := UB.inverse ⋙ G ⋙ UE.functor
  let LFG := UA.inverse ⋙ (F ⋙ G) ⋙ UE.functor
  have hFunctor : LFG = LF ⋙ LG := rfl
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans (nerveMap_comp LF LG).symm
  have hTop : SSet.toTop.map (nerveMap LFG) =
      SSet.toTop.map (nerveMap LF) ≫ SSet.toTop.map (nerveMap LG) :=
    (congrArg SSet.toTop.map hNerve).trans (SSet.toTop.map_comp (nerveMap LF) (nerveMap LG))
  let z := HA.symm x
  have hEval : SSet.toTop.map (nerveMap LFG) z =
      SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z) :=
    (ConcreteCategory.congr_hom hTop z).trans
      (TopCat.comp_app (SSet.toTop.map (nerveMap LF)) (SSet.toTop.map (nerveMap LG)) z)
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG) (HB.symm (HB (SSet.toTop.map (nerveMap LF) z))))
  exact (congrArg HE hEval).trans
    (congrArg (fun y => HE (SSet.toTop.map (nerveMap LG) y))
      (HB.symm_apply_apply (SSet.toTop.map (nerveMap LF) z))).symm

/-- SAME original realized functor maps compose for arbitrary independent source, intermediate and target worlds. -/
public theorem realizedNerveFunctorMap_comp_independent (F : A ⥤ B) (G : B ⥤ E) :
    realizedNerveFunctorMap (F ⋙ G) =
      (realizedNerveFunctorMap G).comp (realizedNerveFunctorMap F) :=
  actualIndependentWorldMapComposition F G

end CategoryTheory

end
