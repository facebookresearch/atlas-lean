/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.UnderSourcePresentation
public import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.UnderSourcePresentation

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {P : C}

example (A : Under P) :
    IsPushout ((Under.costar P).map A.hom) Under.freePointCollapse
      (Under.freeForgetCounit A) (Under.mkIdInitial.to A) :=
  Under.freeSourcePresentationIsPushout A

example (A : Under P) :
    (Under.costar P).map A.hom ≫ Under.freeForgetCounit A =
      Under.freePointCollapse ≫ Under.mkIdInitial.to A :=
  (Under.freeSourcePresentationIsPushout A).w

example (A : Under P) {B : Under P}
    (f : (Under.costar P).obj A.right ⟶ B)
    (g : Under.mk (𝟙 P) ⟶ B)
    (h : (Under.costar P).map A.hom ≫ f = Under.freePointCollapse ≫ g) :
    A ⟶ B :=
  (Under.freeSourcePresentationIsPushout A).desc f g h

example (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ Under P) (A : Under P)
    (hPoint : PreservesColimit F
      (coyoneda.obj (Opposite.op ((Under.costar P).obj P))))
    (hUnderlying : PreservesColimit F
      (coyoneda.obj (Opposite.op ((Under.costar P).obj A.right)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) :=
  Under.source_preservesColimit_of_costarSources κ F A hPoint hUnderlying

#print axioms CategoryTheory.Under.freePointCollapse
#print axioms CategoryTheory.Under.freeForgetCounit
#print axioms CategoryTheory.Under.freeSourcePresentationIsPushout
#print axioms CategoryTheory.Under.identitySource_preservesColimit
#print axioms CategoryTheory.Under.source_preservesColimit_of_costarSources

#lint only unusedArguments in MathlibExt.CategoryTheory.Presentable.UnderSourcePresentation

end MathlibExtTest.UnderSourcePresentation
