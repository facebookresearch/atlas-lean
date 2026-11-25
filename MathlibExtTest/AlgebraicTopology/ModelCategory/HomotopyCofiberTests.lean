/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCofiber

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.HomotopyCofiberTests

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

example : Arrow C ⥤ (WalkingSpan ⥤ C) := cofiberSpan
example : Arrow C ⥤ C := ordinaryCofiber
example : Arrow C ⥤ C := homotopyCofiber
example : homotopyCofiber (C := C) ⟶ ordinaryCofiber :=
  homotopyCofiberComparison

variable (f : Arrow C)

example : ((cofiberSpan (C := C)).obj f).obj WalkingSpan.zero = f.left := rfl
example : ((cofiberSpan (C := C)).obj f).obj WalkingSpan.left = f.right := rfl
example : ((cofiberSpan (C := C)).obj f).obj WalkingSpan.right = ⊤_ C := rfl
example : ((cofiberSpan (C := C)).obj f).map WalkingSpan.Hom.fst = f.hom := rfl
example : ((cofiberSpan (C := C)).obj f).map WalkingSpan.Hom.snd =
    terminal.from f.left := rfl

example (X : C) : Arrow C := Arrow.mk (𝟙 X)

example : (cofiberSpan (C := C)).map (𝟙 f) = 𝟙 _ :=
  (cofiberSpan (C := C)).map_id f

example : (ordinaryCofiber (C := C)).map (𝟙 f) = 𝟙 _ :=
  (ordinaryCofiber (C := C)).map_id f

example : (homotopyCofiber (C := C)).map (𝟙 f) = 𝟙 _ :=
  (homotopyCofiber (C := C)).map_id f

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (cofiberSpan (C := C)).map (sq₁ ≫ sq₂) =
      (cofiberSpan (C := C)).map sq₁ ≫
        (cofiberSpan (C := C)).map sq₂ :=
  (cofiberSpan (C := C)).map_comp sq₁ sq₂

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (ordinaryCofiber (C := C)).map (sq₁ ≫ sq₂) =
      (ordinaryCofiber (C := C)).map sq₁ ≫
        (ordinaryCofiber (C := C)).map sq₂ :=
  (ordinaryCofiber (C := C)).map_comp sq₁ sq₂

example {g h : Arrow C} (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    (homotopyCofiber (C := C)).map (sq₁ ≫ sq₂) =
      (homotopyCofiber (C := C)).map sq₁ ≫
        (homotopyCofiber (C := C)).map sq₂ :=
  (homotopyCofiber (C := C)).map_comp sq₁ sq₂

example : (homotopyCofiberComparison (C := C)).app f =
    (homotopyPushoutComparison (C := C)).app
      ((cofiberSpan (C := C)).obj f) :=
  homotopyCofiberComparison_app f

example {g : Arrow C} (sq : f ⟶ g) :
    (homotopyCofiber (C := C)).map sq ≫
        (homotopyCofiberComparison (C := C)).app g =
      (homotopyCofiberComparison (C := C)).app f ≫
        (ordinaryCofiber (C := C)).map sq :=
  (homotopyCofiberComparison (C := C)).naturality sq

example {g : Arrow C} (sq : f ⟶ g)
    (hleft : WeakEquivalence sq.left)
    (hright : WeakEquivalence sq.right) :
    WeakEquivalence ((homotopyCofiber (C := C)).map sq) :=
  homotopyCofiber_map_weakEquivalence sq hleft hright

example [IsCofibrant f.left] [IsCofibrant (⊤_ C)] [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyCofiberComparison_of_cofibration f

example [IsCofibrant f.left] [IsCofibrant f.right]
    [Cofibration (terminal.from f.left)] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyCofiberComparison_of_terminalLeg f

example [HasZeroObject C] [IsCofibrant f.left] [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyCofiberComparison_of_pointedCofibration f

example [IsLeftProper C] [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyCofiberComparison_of_leftProper f

example [IsLeftProper C] [Cofibration (terminal.from f.left)] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) :=
  weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg f

section Falsifiers

example : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) := by infer_instance
  trivial

example [IsCofibrant (⊤_ C)] [Cofibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_cofibration f
  trivial

example [IsCofibrant f.left] [Cofibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_cofibration f
  trivial

example [IsCofibrant f.left] [IsCofibrant (⊤_ C)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_cofibration f
  trivial

example [IsCofibrant f.right]
    [Cofibration (terminal.from f.left)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_terminalLeg f
  trivial

example [IsCofibrant f.left]
    [Cofibration (terminal.from f.left)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_terminalLeg f
  trivial

example [IsCofibrant f.left] [IsCofibrant f.right] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_terminalLeg f
  trivial

example [IsCofibrant f.left] [Cofibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_pointedCofibration f
  trivial

example [Cofibration f.hom] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_leftProper f
  trivial

example [IsLeftProper C] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_leftProper f
  trivial

example [Cofibration (terminal.from f.left)] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg f
  trivial

example [IsLeftProper C] : True := by
  fail_if_success
    have _ : WeakEquivalence
        ((homotopyCofiberComparison (C := C)).app f) :=
      weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg f
  trivial

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyCofiberPointQuotientIso
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyCofiberMappingConeIso
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyCofiberLocalization
  fail_if_success
    let _ := HomotopicalAlgebra.homotopyCofiberHoUniversalProperty
  trivial

end Falsifiers

section MissingFactorization

variable {D : Type u} [Category.{v} D] [ModelCategory D]

example : True := by
  fail_if_success
    have _ : Arrow D ⥤ D := homotopyCofiber
  fail_if_success
    have _ : homotopyCofiber (C := D) ⟶ ordinaryCofiber :=
      homotopyCofiberComparison
  trivial

end MissingFactorization

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [HasFunctorialFactorization (cofibrations C₁)
  (trivialFibrations C₁)]

example : Arrow C₁ ⥤ (WalkingSpan ⥤ C₁) := cofiberSpan
example : Arrow C₁ ⥤ C₁ := ordinaryCofiber
example : Arrow C₁ ⥤ C₁ := homotopyCofiber
example : homotopyCofiber (C := C₁) ⟶ ordinaryCofiber :=
  homotopyCofiberComparison

end UniverseOneZero

end HomotopicalAlgebra.HomotopyCofiberTests

#check HomotopicalAlgebra.cofiberSpan
#check HomotopicalAlgebra.ordinaryCofiber
#check HomotopicalAlgebra.homotopyCofiber
#check HomotopicalAlgebra.homotopyCofiberComparison
#check HomotopicalAlgebra.homotopyCofiberComparison_app
#check HomotopicalAlgebra.homotopyCofiber_map_weakEquivalence
#check
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_cofibration
#check
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_terminalLeg
#check
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_pointedCofibration
#check
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_leftProper
#check
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg

#print axioms HomotopicalAlgebra.cofiberSpan
#print axioms HomotopicalAlgebra.ordinaryCofiber
#print axioms HomotopicalAlgebra.homotopyCofiber
#print axioms HomotopicalAlgebra.homotopyCofiberComparison
#print axioms HomotopicalAlgebra.homotopyCofiberComparison_app
#print axioms HomotopicalAlgebra.homotopyCofiber_map_weakEquivalence
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_cofibration
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_terminalLeg
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_pointedCofibration
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_leftProper
#print axioms
  HomotopicalAlgebra.weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg

end
