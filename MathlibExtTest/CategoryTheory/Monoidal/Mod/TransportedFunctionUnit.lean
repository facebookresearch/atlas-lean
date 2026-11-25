/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.TransportedFunctionUnit

/-!
# Public clients of transported module function units

The clients retain an arbitrary commutative coefficient, the full original
module equivalence and both transformations of its parametrized adjunction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj MonoidalClosed
open CategoryTheory.Mod.EquivalenceFunctionTransport

namespace TransportedFunctionUnitClient

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

example {S T : D} (f : S ⟶ T) :
    HEq ((smashBifunctor A E).map f) (sourceSmashMap A E f) :=
  FunctionUnit.sourceSmashMap_heq A E f

example {S T : D} (f : S ⟶ T) (unitIso : functor A E T ≅ 𝟭 D) (X : D) :
    ((adjunction A E S).homEquiv X X)
      ((sourceSmashMap A E f).app X ≫
        (FunctionUnitAdjunction.leftUnitIso (adjunction A E T) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (precompose A E f).app X :=
  FunctionUnit.sourcePre_unit_adjoint A E f unitIso X

example {S T : D} (f : S ⟶ T) (unitIso : functor A E T ≅ 𝟭 D) (X : D) :
    ((adjunction A E S).homEquiv X X).symm
      (unitIso.inv.app X ≫ (precompose A E f).app X) =
      (sourceSmashMap A E f).app X ≫
        (FunctionUnitAdjunction.leftUnitIso (adjunction A E T) unitIso).hom.app X :=
  FunctionUnit.sourcePre_unit_uncurried A E f unitIso X

example (S X : D) :
    (smashFunctor A E S).map ((adjunction A E S).unit.app X) ≫
      (adjunction A E S).counit.app ((smashFunctor A E S).obj X) =
      𝟙 ((smashFunctor A E S).obj X) :=
  (adjunction A E S).left_triangle_components X

example (S Y : D) :
    (adjunction A E S).unit.app ((functor A E S).obj Y) ≫
      (functor A E S).map ((adjunction A E S).counit.app Y) =
      𝟙 ((functor A E S).obj Y) :=
  (adjunction A E S).right_triangle_components Y

end TransportedFunctionUnitClient
