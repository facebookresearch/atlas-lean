/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialHomotopyFiberCofiber
import Batteries.Tactic.Lint

/-! # Canonical zero-diagram universal properties and full original caller maps -/

public section
set_option autoImplicit false
noncomputable section
universe v u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace OriginalHomotopyFiberCofiberClients

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
/-- Every original fiber cone keeps every canonical replacement-unit leg. -/
theorem everyFiberCone (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f)) :
    ∀ j, homotopyFiberLift f c ≫ homotopyFiberProjection f j =
      c.π.app j ≫
        ((homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)).app j :=
  homotopyFiberLift_projection f c

omit [HasZeroObject C]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- Every original cofiber cocone keeps every canonical replacement-counit leg. -/
theorem everyCofiberCocone (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f)) :
    ∀ j, homotopyCofiberInjection f j ≫ homotopyCofiberDesc f c =
      ((homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f)).app j ≫ c.ι.app j :=
  homotopyCofiberInjection_desc f c

/-- Both canonical functors preserve every original square weak at both endpoints. -/
theorem bothWholeWeakSquares {f g : Arrow C} (sq : f ⟶ g)
    (hs : WeakEquivalence sq.left) (ht : WeakEquivalence sq.right) :
    WeakEquivalence ((homotopyFiber (C := C)).map sq) ∧
      WeakEquivalence ((homotopyCofiber (C := C)).map sq) :=
  ⟨homotopyFiber_map_weakEquivalence sq hs ht, homotopyCofiber_map_weakEquivalence sq hs ht⟩

/-- The same canonical square maps retain all fiber projections and cofiber injections. -/
theorem allOriginalSquareLegs {f g : Arrow C} (sq : f ⟶ g) :
    (∀ j, (homotopyFiber (C := C)).map sq ≫ homotopyFiberProjection g j =
      homotopyFiberProjection f j ≫ ((homotopyFiberDiagram (C := C)).map sq).app j) ∧
    (∀ j, homotopyCofiberInjection f j ≫ (homotopyCofiber (C := C)).map sq =
      ((homotopyCofiberDiagram (C := C)).map sq).app j ≫ homotopyCofiberInjection g j) :=
  ⟨homotopyFiber_map_projection sq, homotopyCofiberInjection_map sq⟩

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
/-- Every whole canonical fiber map is determined by all original replaced legs. -/
theorem fullFiberUniqueness (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f))
    (m : c.pt ⟶ (homotopyFiber (C := C)).obj f)
    (hm : ∀ j, m ≫ homotopyFiberProjection f j =
      c.π.app j ≫
        ((homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)).app j) :
    m = homotopyFiberLift f c := homotopyFiberLift_unique f c m hm

omit [HasZeroObject C]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)] in
/-- Every whole canonical cofiber map is determined by all original replaced legs. -/
theorem fullCofiberUniqueness (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f))
    (m : (homotopyCofiber (C := C)).obj f ⟶ c.pt)
    (hm : ∀ j, homotopyCofiberInjection f j ≫ m =
      ((homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f)).app j ≫ c.ι.app j) :
    m = homotopyCofiberDesc f c := homotopyCofiberDesc_unique f c m hm

example (f : Arrow C) : (homotopyFiberCone f).pt = (homotopyFiber (C := C)).obj f := rfl
example (f : Arrow C) : IsLimit (homotopyFiberCone f) := homotopyFiberConeIsLimit f
example (f : Arrow C) : (homotopyCofiberCocone f).pt = (homotopyCofiber (C := C)).obj f := rfl
example (f : Arrow C) : IsColimit (homotopyCofiberCocone f) := homotopyCofiberCoconeIsColimit f

example (F : WalkingCospan ⥤ C) :
    (homotopyPullbackReplacement F).P = homotopyPullbackReplacementFunctor.obj F :=
  homotopyPullbackReplacement_P F
example (F : WalkingCospan ⥤ C) :
    (homotopyPullbackReplacement F).unit ≫ eqToHom (homotopyPullbackReplacement_P F) =
      homotopyPullbackReplacementUnit.app F := homotopyPullbackReplacement_unit F
example (F : WalkingSpan ⥤ C) :
    (homotopyPushoutReplacement F).Q = homotopyPushoutReplacementFunctor.obj F :=
  homotopyPushoutReplacement_Q F
example (F : WalkingSpan ⥤ C) :
    eqToHom (homotopyPushoutReplacement_Q F).symm ≫ (homotopyPushoutReplacement F).counit =
      homotopyPushoutReplacementCounit.app F := homotopyPushoutReplacement_counit F

end OriginalHomotopyFiberCofiberClients

#print axioms homotopyFiberConeIsLimit
#print axioms homotopyCofiberCoconeIsColimit
#print axioms OriginalHomotopyFiberCofiberClients.bothWholeWeakSquares
#print axioms OriginalHomotopyFiberCofiberClients.allOriginalSquareLegs
#print axioms OriginalHomotopyFiberCofiberClients.fullFiberUniqueness
#print axioms OriginalHomotopyFiberCofiberClients.fullCofiberUniqueness
#print axioms homotopyPullbackReplacement
#print axioms homotopyPushoutReplacement
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorialHomotopyFiberCofiber
