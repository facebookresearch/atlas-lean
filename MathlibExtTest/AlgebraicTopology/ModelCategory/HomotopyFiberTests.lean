/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFiber

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.HomotopyFiberTests

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasZeroObject C]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

section Core

example : Arrow C ⥤ (WalkingCospan ⥤ C) := fiberCospan
example : Arrow C ⥤ C := ordinaryFiber
example : Arrow C ⥤ C := homotopyFiber
example : ordinaryFiber (C := C) ⟶ homotopyFiber :=
  homotopyFiberComparison

variable (f : Arrow C)

example : ((fiberCospan (C := C)).obj f).obj WalkingCospan.one =
    f.right := rfl

example : ((fiberCospan (C := C)).obj f).obj WalkingCospan.left =
    f.left := rfl

example : ((fiberCospan (C := C)).obj f).obj WalkingCospan.right =
    ⊥_ C := rfl

example : ((fiberCospan (C := C)).obj f).map WalkingCospan.Hom.inl =
    f.hom := rfl

example : ((fiberCospan (C := C)).obj f).map WalkingCospan.Hom.inr =
    initial.to f.right := rfl

example {g : Arrow C} (sq : f ⟶ g) :
    ((fiberCospan (C := C)).map sq).app WalkingCospan.one = sq.right := rfl

example {g : Arrow C} (sq : f ⟶ g) :
    ((fiberCospan (C := C)).map sq).app WalkingCospan.left = sq.left := rfl

example {g : Arrow C} (sq : f ⟶ g) :
    ((fiberCospan (C := C)).map sq).app WalkingCospan.right = 𝟙 _ := rfl

example : (fiberCospan (C := C)).map (𝟙 f) = 𝟙 _ :=
  (fiberCospan (C := C)).map_id f

example : (ordinaryFiber (C := C)).map (𝟙 f) = 𝟙 _ :=
  (ordinaryFiber (C := C)).map_id f

example : (homotopyFiber (C := C)).map (𝟙 f) = 𝟙 _ :=
  (homotopyFiber (C := C)).map_id f

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (fiberCospan (C := C)).map (sq₁ ≫ sq₂) =
      (fiberCospan (C := C)).map sq₁ ≫
        (fiberCospan (C := C)).map sq₂ :=
  (fiberCospan (C := C)).map_comp sq₁ sq₂

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (ordinaryFiber (C := C)).map (sq₁ ≫ sq₂) =
      (ordinaryFiber (C := C)).map sq₁ ≫
        (ordinaryFiber (C := C)).map sq₂ :=
  (ordinaryFiber (C := C)).map_comp sq₁ sq₂

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (homotopyFiber (C := C)).map (sq₁ ≫ sq₂) =
      (homotopyFiber (C := C)).map sq₁ ≫
        (homotopyFiber (C := C)).map sq₂ :=
  (homotopyFiber (C := C)).map_comp sq₁ sq₂

example : (homotopyFiberComparison (C := C)).app f =
    (homotopyPullbackComparison (C := C)).app
      ((fiberCospan (C := C)).obj f) :=
  homotopyFiberComparison_app f

example {g : Arrow C} (sq : f ⟶ g) :
    (ordinaryFiber (C := C)).map sq ≫
        (homotopyFiberComparison (C := C)).app g =
      (homotopyFiberComparison (C := C)).app f ≫
        (homotopyFiber (C := C)).map sq :=
  (homotopyFiberComparison (C := C)).naturality sq

end Core

section PointwiseWeak

variable {f g : Arrow C} (sq : f ⟶ g)
variable (hleft : WeakEquivalence sq.left)
variable (hright : WeakEquivalence sq.right)

example : WeakEquivalence ((homotopyFiber (C := C)).map sq) :=
  homotopyFiber_map_weakEquivalence sq hleft hright

end PointwiseWeak

section ComparisonCriteria

variable (f : Arrow C)

example [IsFibrant f.right] [Fibration f.hom] :
    WeakEquivalence ((homotopyFiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyFiberComparison_of_fibration_fibrant f

section RightProper

variable [IsRightProper C]

example [Fibration f.hom] :
    WeakEquivalence ((homotopyFiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyFiberComparison_of_rightProper f

end RightProper

end ComparisonCriteria

section IdentityIsoZero

variable {X Y : C}

example [IsFibrant X] :
    WeakEquivalence
      ((homotopyFiberComparison (C := C)).app (Arrow.mk (𝟙 X))) := by
  let _ : Fibration (Arrow.mk (𝟙 X)).hom := by
    change Fibration (𝟙 X)
    infer_instance
  let _ : IsFibrant (Arrow.mk (𝟙 X)).right := by
    change IsFibrant X
    infer_instance
  apply weakEquivalence_homotopyFiberComparison_of_fibration_fibrant

example (f : X ⟶ Y) [IsIso f] [IsFibrant Y] :
    WeakEquivalence
      ((homotopyFiberComparison (C := C)).app (Arrow.mk f)) := by
  let _ : Fibration (Arrow.mk f).hom := by
    change Fibration f
    infer_instance
  let _ : IsFibrant (Arrow.mk f).right := by
    change IsFibrant Y
    infer_instance
  apply weakEquivalence_homotopyFiberComparison_of_fibration_fibrant

section RightProper

variable [IsRightProper C]

example : WeakEquivalence
    ((homotopyFiberComparison (C := C)).app
      (Arrow.mk (𝟙 (⊥_ C)))) := by
  let _ : Fibration (Arrow.mk (𝟙 (⊥_ C))).hom := by
    change Fibration (𝟙 (⊥_ C))
    infer_instance
  apply weakEquivalence_homotopyFiberComparison_of_rightProper

example : WeakEquivalence
    ((homotopyFiberComparison (C := C)).app
      (Arrow.mk (𝟙 (⊤_ C)))) := by
  let _ : Fibration (Arrow.mk (𝟙 (⊤_ C))).hom := by
    change Fibration (𝟙 (⊤_ C))
    infer_instance
  apply weakEquivalence_homotopyFiberComparison_of_rightProper

end RightProper

end IdentityIsoZero

section Falsifiers

variable (f : Arrow C)

example : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyFiberComparison (C := C)).app f) := by infer_instance
  trivial

example [IsFibrant f.right] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyFiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyFiberComparison_of_fibration_fibrant f
  trivial

example [Fibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyFiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyFiberComparison_of_fibration_fibrant f
  trivial

example [Fibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyFiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyFiberComparison_of_rightProper f
  trivial

example [IsRightProper C] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyFiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyFiberComparison_of_rightProper f
  trivial

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.isFibrant_initial_of_hasZeroObject
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyFiberIso
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyFiberLocalization
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyFiberHoUniversalProperty
  trivial

end Falsifiers

section MissingFactorization

variable {D : Type u} [Category.{v} D] [ModelCategory D]
variable [HasZeroObject D]

example : Arrow D ⥤ (WalkingCospan ⥤ D) := fiberCospan
example : Arrow D ⥤ D := ordinaryFiber

example : True := by
  fail_if_success
    have _ : Arrow D ⥤ D := homotopyFiber
  fail_if_success
    have _ : ordinaryFiber (C := D) ⟶ homotopyFiber :=
      homotopyFiberComparison
  trivial

end MissingFactorization

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [HasZeroObject C₁]
variable [HasFunctorialFactorization
  (trivialCofibrations C₁) (fibrations C₁)]

example : Arrow C₁ ⥤ (WalkingCospan ⥤ C₁) := fiberCospan
example : Arrow C₁ ⥤ C₁ := ordinaryFiber
example : Arrow C₁ ⥤ C₁ := homotopyFiber
example : ordinaryFiber (C := C₁) ⟶ homotopyFiber :=
  homotopyFiberComparison

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
variable [HasZeroObject C₀]
variable [HasFunctorialFactorization
  (trivialCofibrations C₀) (fibrations C₀)]

example : Arrow C₀ ⥤ (WalkingCospan ⥤ C₀) := fiberCospan
example : Arrow C₀ ⥤ C₀ := ordinaryFiber
example : Arrow C₀ ⥤ C₀ := homotopyFiber

end UniverseOneZero

end HomotopicalAlgebra.HomotopyFiberTests

#check HomotopicalAlgebra.fiberCospan
#check HomotopicalAlgebra.ordinaryFiber
#check HomotopicalAlgebra.homotopyFiber
#check HomotopicalAlgebra.homotopyFiberComparison
#check HomotopicalAlgebra.homotopyFiberComparison_app
#check HomotopicalAlgebra.homotopyFiber_map_weakEquivalence
#check
  HomotopicalAlgebra.weakEquivalence_homotopyFiberComparison_of_fibration_fibrant
#check HomotopicalAlgebra.weakEquivalence_homotopyFiberComparison_of_rightProper

#print axioms HomotopicalAlgebra.fiberCospan
#print axioms HomotopicalAlgebra.ordinaryFiber
#print axioms HomotopicalAlgebra.homotopyFiber
#print axioms HomotopicalAlgebra.homotopyFiberComparison
#print axioms HomotopicalAlgebra.homotopyFiberComparison_app
#print axioms HomotopicalAlgebra.homotopyFiber_map_weakEquivalence
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyFiberComparison_of_fibration_fibrant
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyFiberComparison_of_rightProper

end
