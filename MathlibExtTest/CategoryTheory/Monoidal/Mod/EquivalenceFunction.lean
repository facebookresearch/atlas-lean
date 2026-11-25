/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction
import Mathlib.Tactic

/-!
# Original carrier transport and source naturality

These clients retain arbitrary base and carrier categories, independent universes,
the actual module monoid, and the chosen complete carrier equivalence. The triangle
and target naturality checks use the standard adjunction API directly.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace MathlibExtTest.ModuleFunctionTransport

open CategoryTheory.Mod.EquivalenceFunctionTransport

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

local instance : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
local instance : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

example (X : D) : functor A E X =
    E.inverse ⋙ Mod.internalHomOfEqualizer A (E.inverse.obj X) ⋙ E.functor :=
  sourceFunctor_obj A E (E.inverse.obj X)

example (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (functor A E X).map f =
      E.functor.map ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).map (E.inverse.map f)) :=
  functor_map A E X f

example {X Y : D} (f : X ⟶ Y) (Z : D) :
    (precompose A E f).app Z =
      E.functor.map ((MonoidalClosed.pre (E.inverse.map f)).app (E.inverse.obj Z)) :=
  precompose_app A E f Z

example (X Y : D) :
    (adjunction A E X).unit.app Y =
      E.symm.toAdjunction.unit.app Y ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A
          (E.inverse.obj X)).unit.app (E.inverse.obj Y)) ≫
        E.functor.map ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).map
          (E.toAdjunction.unit.app
            (((Mod.relativeTensor A).obj (E.inverse.obj X)).obj (E.inverse.obj Y)))) :=
  adjunction_unit_app A E X Y

example (X Y : D) :
    (adjunction A E X).counit.app Y =
      E.functor.map (((Mod.relativeTensor A).obj (E.inverse.obj X)).map
        (E.symm.toAdjunction.counit.app
          ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).obj (E.inverse.obj Y)))) ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A
          (E.inverse.obj X)).counit.app (E.inverse.obj Y)) ≫
        E.toAdjunction.counit.app Y :=
  adjunction_counit_app A E X Y

example {X Y : D} (f : X ⟶ Y) (Z : D) :
    (adjunction A E Y).unit.app Z ≫
        (precompose A E f).app ((smashFunctor A E Y).obj Z) =
      (adjunction A E X).unit.app Z ≫
        (functor A E X).map ((sourceSmashMap A E f).app Z) :=
  adjunction_unit_source A E f Z

example {X Y : D} (f : X ⟶ Y) (Z : D) :
    (sourceSmashMap A E f).app ((functor A E Y).obj Z) ≫
        (adjunction A E Y).counit.app Z =
      (smashFunctor A E X).map ((precompose A E f).app Z) ≫
        (adjunction A E X).counit.app Z :=
  adjunction_counit_source A E f Z

example (X : D) {Y Z : D} (f : Y ⟶ Z) :
    f ≫ (adjunction A E X).unit.app Z =
      (adjunction A E X).unit.app Y ≫
        (functor A E X).map ((smashFunctor A E X).map f) :=
  (adjunction A E X).unit.naturality f

example (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (smashFunctor A E X).map ((functor A E X).map f) ≫
        (adjunction A E X).counit.app Z =
      (adjunction A E X).counit.app Y ≫ f :=
  (adjunction A E X).counit.naturality f

example (X Y : D) :
    (smashFunctor A E X).map ((adjunction A E X).unit.app Y) ≫
        (adjunction A E X).counit.app ((smashFunctor A E X).obj Y) =
      𝟙 ((smashFunctor A E X).obj Y) :=
  (adjunction A E X).left_triangle_components Y

example (X Y : D) :
    (adjunction A E X).unit.app ((functor A E X).obj Y) ≫
        (functor A E X).map ((adjunction A E X).counit.app Y) =
      𝟙 ((functor A E X).obj Y) :=
  (adjunction A E X).right_triangle_components Y

example (X : D) : sourceSmashMap A E (𝟙 X) = 𝟙 (smashFunctor A E X) :=
  (smashBifunctor A E).map_id X

example {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceSmashMap A E (f ≫ g) = sourceSmashMap A E f ≫ sourceSmashMap A E g :=
  (smashBifunctor A E).map_comp f g

#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.functor_map
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.smashFunctor_map
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.precompose_app
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.adjunction_unit_app
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.adjunction_counit_app
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.smashBifunctor
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.smashBifunctor_obj
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap_app
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.adjunction_unit_source
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.adjunction_counit_source

example : smashBifunctor A E ⊣₂ bifunctor A E := parametrizedAdjunction A E

example (X : D) : (parametrizedAdjunction A E).adj X = adjunction A E X :=
  parametrizedAdjunction_adj A E X

example (X Y : D) :
    ((parametrizedAdjunction A E).adj X).unit.app Y =
      E.symm.toAdjunction.unit.app Y ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A
          (E.inverse.obj X)).unit.app (E.inverse.obj Y)) ≫
        E.functor.map ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).map
          (E.toAdjunction.unit.app
            (((Mod.relativeTensor A).obj (E.inverse.obj X)).obj (E.inverse.obj Y)))) := by
  rw [parametrizedAdjunction_adj]
  exact adjunction_unit_app A E X Y

example (X Y : D) :
    ((parametrizedAdjunction A E).adj X).counit.app Y =
      E.functor.map (((Mod.relativeTensor A).obj (E.inverse.obj X)).map
        (E.symm.toAdjunction.counit.app
          ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).obj (E.inverse.obj Y)))) ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A
          (E.inverse.obj X)).counit.app (E.inverse.obj Y)) ≫
        E.toAdjunction.counit.app Y := by
  rw [parametrizedAdjunction_adj]
  exact adjunction_counit_app A E X Y

example {X Y : D} (f : X ⟶ Y) :
    ((parametrizedAdjunction A E).adj X).unit ≫
        Functor.whiskerRight ((smashBifunctor A E).map f) ((bifunctor A E).obj (.op X)) =
      ((parametrizedAdjunction A E).adj Y).unit ≫
        Functor.whiskerLeft ((smashBifunctor A E).obj Y) ((bifunctor A E).map f.op) :=
  (parametrizedAdjunction A E).unit_whiskerRight_map f

example {X Y : D} (f : X ⟶ Y) :
    Functor.whiskerLeft ((bifunctor A E).obj (.op Y)) ((smashBifunctor A E).map f) ≫
        ((parametrizedAdjunction A E).adj Y).counit =
      Functor.whiskerRight ((bifunctor A E).map f.op) ((smashBifunctor A E).obj X) ≫
        ((parametrizedAdjunction A E).adj X).counit :=
  (parametrizedAdjunction A E).whiskerLeft_map_counit f

example {X Y Z W : D} (f : X ⟶ Y) (g : (smashFunctor A E Y).obj Z ⟶ W) :
    (parametrizedAdjunction A E).homEquiv ((sourceSmashMap A E f).app Z ≫ g) =
      (parametrizedAdjunction A E).homEquiv g ≫ (precompose A E f).app W :=
  (parametrizedAdjunction A E).homEquiv_naturality_one f g

example {X Y Z W : D} (f : X ⟶ Y) (g : Z ⟶ (functor A E Y).obj W) :
    (parametrizedAdjunction A E).homEquiv.symm (g ≫ (precompose A E f).app W) =
      (sourceSmashMap A E f).app Z ≫ (parametrizedAdjunction A E).homEquiv.symm g :=
  (parametrizedAdjunction A E).homEquiv_symm_naturality_one f g

#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.parametrizedAdjunction
#print axioms CategoryTheory.Mod.EquivalenceFunctionTransport.parametrizedAdjunction_adj

section Compatibility

example : smashBifunctor A E ⊣₂ bifunctor A E := by
  fail_if_success exact NativeOmegaPreparation.ModuleFunctionTransport.parametrizedAdjunction A E
  exact parametrizedAdjunction A E

example : NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E = sourceFunctor A E := rfl

example (M : Mod C A.X) :
    NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M =
      sourceFunctor_obj A E M := rfl

example (M : Mod C A.X) :
    NativeOmegaPreparation.ModuleFunctionTransport.sourceAdjunction A E M = sourceAdjunction A E M := rfl

example : NativeOmegaPreparation.ModuleFunctionTransport.bifunctor A E = bifunctor A E := rfl

example (X : D) : NativeOmegaPreparation.ModuleFunctionTransport.functor A E X = functor A E X := rfl

example (X : D) :
    NativeOmegaPreparation.ModuleFunctionTransport.smashFunctor A E X = smashFunctor A E X := rfl

example (X : D) :
    NativeOmegaPreparation.ModuleFunctionTransport.adjunction A E X = adjunction A E X := rfl

example {X Y : D} (f : X ⟶ Y) :
    NativeOmegaPreparation.ModuleFunctionTransport.precompose A E f = precompose A E f := rfl

example (M : Mod C A.X) (X : D) (e : M ≅ E.inverse.obj X) :
    NativeOmegaPreparation.ModuleFunctionTransport.sourceComparison A E M X e =
      sourceComparison A E M X e := rfl

end Compatibility

#lint only unusedArguments in MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction

end MathlibExtTest.ModuleFunctionTransport
