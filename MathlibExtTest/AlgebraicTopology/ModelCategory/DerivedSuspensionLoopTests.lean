/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoop

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.CategoryTheory.Preadditive.Basic
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty
open scoped ZeroObject

namespace HomotopicalAlgebra.DerivedSuspensionLoopTests

section Generic

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasZeroObject C]
variable [HasFunctorialFactorization
  (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

example : C ⥤ C := derivedSuspension
example : C ⥤ C := derivedLoop

example (X : C) :
    (derivedSuspension (C := C)).obj X =
      (homotopyCofiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsTerminal.from X)) :=
  derivedSuspension_obj X

example (X : C) :
    (derivedLoop (C := C)).obj X =
      (homotopyFiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsInitial.to X)) :=
  derivedLoop_obj X

example (X : C) :
    WeakEquivalence ((derivedSuspension (C := C)).map (𝟙 X)) :=
  derivedSuspension_map_weakEquivalence (𝟙 X) (by infer_instance)

example (X : C) :
    WeakEquivalence ((derivedLoop (C := C)).map (𝟙 X)) :=
  derivedLoop_map_weakEquivalence (𝟙 X) (by infer_instance)

example {X Y : C} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    WeakEquivalence ((derivedSuspension (C := C)).map f) :=
  derivedSuspension_map_weakEquivalence f hf

example {X Y : C} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    WeakEquivalence ((derivedLoop (C := C)).map f) :=
  derivedLoop_map_weakEquivalence f hf

example :
    (derivedSuspension (C := C)).obj (0 : C) =
      (homotopyCofiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsTerminal.from (0 : C))) :=
  derivedSuspension_obj (0 : C)

example :
    (derivedLoop (C := C)).obj (0 : C) =
      (homotopyFiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsInitial.to (0 : C))) :=
  derivedLoop_obj (0 : C)

example :
    WeakEquivalence ((derivedSuspension (C := C)).map (𝟙 (0 : C))) :=
  derivedSuspension_map_weakEquivalence (𝟙 (0 : C)) (by infer_instance)

example : WeakEquivalence ((derivedLoop (C := C)).map (𝟙 (0 : C))) :=
  derivedLoop_map_weakEquivalence (𝟙 (0 : C)) (by infer_instance)

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.zeroOutArrow (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.zeroInArrow (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedSuspensionLoopAdjunction (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedSuspensionLoopUnit (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedSuspensionLoopCounit (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedSuspensionLoopEquivalence (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedSuspensionLocalization (C := C)
  fail_if_success
    let _ := HomotopicalAlgebra.derivedLoopLocalization (C := C)
  trivial

end Generic

section PremiseDeletion

section MissingZeroObject

variable {D : Type u} [Category.{v} D] [ModelCategory D]
variable [HasFunctorialFactorization
  (cofibrations D) (trivialFibrations D)]
variable [HasFunctorialFactorization
  (trivialCofibrations D) (fibrations D)]

example : True := by
  fail_if_success
    have _ : D ⥤ D := derivedSuspension (C := D)
  fail_if_success
    have _ : D ⥤ D := derivedLoop (C := D)
  trivial

end MissingZeroObject

section MissingSuspensionFactorization

variable {D : Type u} [Category.{v} D] [ModelCategory D] [HasZeroObject D]
variable [HasFunctorialFactorization
  (trivialCofibrations D) (fibrations D)]

example : D ⥤ D := derivedLoop

example : True := by
  fail_if_success
    have _ : D ⥤ D := derivedSuspension (C := D)
  trivial

end MissingSuspensionFactorization

section MissingLoopFactorization

variable {D : Type u} [Category.{v} D] [ModelCategory D] [HasZeroObject D]
variable [HasFunctorialFactorization
  (cofibrations D) (trivialFibrations D)]

example : D ⥤ D := derivedSuspension

example : True := by
  fail_if_success
    have _ : D ⥤ D := derivedLoop (C := D)
  trivial

end MissingLoopFactorization

end PremiseDeletion

section Universes

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [HasZeroObject C₁]
variable [HasFunctorialFactorization
  (cofibrations C₁) (trivialFibrations C₁)]
variable [HasFunctorialFactorization
  (trivialCofibrations C₁) (fibrations C₁)]

example : C₁ ⥤ C₁ := derivedSuspension
example : C₁ ⥤ C₁ := derivedLoop

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
variable [HasZeroObject C₀]
variable [HasFunctorialFactorization
  (cofibrations C₀) (trivialFibrations C₀)]
variable [HasFunctorialFactorization
  (trivialCofibrations C₀) (fibrations C₀)]

example : C₀ ⥤ C₀ := derivedSuspension
example : C₀ ⥤ C₀ := derivedLoop

end Universes

section GenuinePointedModel

open scoped CochainComplex.Plus.modelCategoryQuillen

local notation "ConcretePointedModel" =>
  CochainComplex.Plus AddCommGrpCat

local instance : HasZeroObject ConcretePointedModel :=
  Preadditive.hasZeroObject_of_hasCoproduct.{0, _, _} _

#synth ModelCategory ConcretePointedModel
#synth HasZeroObject ConcretePointedModel

variable [HasFunctorialFactorization
  (cofibrations ConcretePointedModel)
    (trivialFibrations ConcretePointedModel)]
variable [HasFunctorialFactorization
  (trivialCofibrations ConcretePointedModel)
    (fibrations ConcretePointedModel)]

example : ConcretePointedModel ⥤ ConcretePointedModel := derivedSuspension
example : ConcretePointedModel ⥤ ConcretePointedModel := derivedLoop

example (X : ConcretePointedModel) :
    WeakEquivalence
      ((derivedSuspension (C := ConcretePointedModel)).map (𝟙 X)) :=
  derivedSuspension_map_weakEquivalence (𝟙 X) (by infer_instance)

example (X : ConcretePointedModel) :
    WeakEquivalence ((derivedLoop (C := ConcretePointedModel)).map (𝟙 X)) :=
  derivedLoop_map_weakEquivalence (𝟙 X) (by infer_instance)

example {X Y : ConcretePointedModel} (e : X ≅ Y) :
    WeakEquivalence
      ((derivedSuspension (C := ConcretePointedModel)).map e.hom) :=
  derivedSuspension_map_weakEquivalence e.hom (by infer_instance)

example {X Y : ConcretePointedModel} (e : X ≅ Y) :
    WeakEquivalence ((derivedLoop (C := ConcretePointedModel)).map e.hom) :=
  derivedLoop_map_weakEquivalence e.hom (by infer_instance)

end GenuinePointedModel

section UnpointedTopCat

open scoped TopCat.modelCategory

example : True := by
  fail_if_success
    let _ : HasZeroObject TopCat.{u} := inferInstance
  fail_if_success
    let _ := TopCat.derivedSuspension
  fail_if_success
    let _ := TopCat.derivedLoop
  trivial

end UnpointedTopCat

end HomotopicalAlgebra.DerivedSuspensionLoopTests

#check HomotopicalAlgebra.derivedSuspension
#check HomotopicalAlgebra.derivedSuspension_obj
#check HomotopicalAlgebra.derivedSuspension_map_weakEquivalence
#check HomotopicalAlgebra.derivedLoop
#check HomotopicalAlgebra.derivedLoop_obj
#check HomotopicalAlgebra.derivedLoop_map_weakEquivalence

#print axioms HomotopicalAlgebra.derivedSuspension
#print axioms HomotopicalAlgebra.derivedSuspension_obj
#print axioms HomotopicalAlgebra.derivedSuspension_map_weakEquivalence
#print axioms HomotopicalAlgebra.derivedLoop
#print axioms HomotopicalAlgebra.derivedLoop_obj
#print axioms HomotopicalAlgebra.derivedLoop_map_weakEquivalence

end
