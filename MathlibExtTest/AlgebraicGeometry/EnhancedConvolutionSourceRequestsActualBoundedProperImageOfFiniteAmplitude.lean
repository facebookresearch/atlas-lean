/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedProperImageOfFiniteAmplitude

/-!
# Bounded proper image functor from the finite-amplitude condition

The proved boundedness source promotes the native derived proper image
to the full bounded derived categories, acting as the original functor
on objects and maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedProperImageOfFiniteAmplitude

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open MathlibExt.AlgebraicGeometry.BoundedIndImageModels
open WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests

local instance testAbelianPreadditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- The bounded proper image functor from the finite-amplitude condition. -/
def boundedProperImageOfFiniteAmplitude (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    [(derivedIndProperImage k f P D E).IsTriangulated]
    (h : FiniteProperImageAmplitude k f P D E) :
    BoundedIndDerived k X ⥤ BoundedIndDerived k Y :=
  boundedProperImage k f P D E
    (actual_bounded_proper_image_of_finite_amplitude k X Y f P D E h)

/-- The promoted functor acts as the native derived proper image on objects. -/
theorem boundedProperImageOfFiniteAmplitude_obj (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    [(derivedIndProperImage k f P D E).IsTriangulated]
    (h : FiniteProperImageAmplitude k f P D E) (K : BoundedIndDerived k X) :
    ((boundedProperImageOfFiniteAmplitude k X Y f P D E h).obj K).obj =
      (derivedIndProperImage k f P D E).obj K.obj := rfl

/-- The promoted functor acts as the native derived proper image on maps. -/
theorem boundedProperImageOfFiniteAmplitude_map (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    [(derivedIndProperImage k f P D E).IsTriangulated]
    (h : FiniteProperImageAmplitude k f P D E) {K L : BoundedIndDerived k X}
    (a : K ⟶ L) :
    ((boundedProperImageOfFiniteAmplitude k X Y f P D E h).map a).hom =
      (derivedIndProperImage k f P D E).map a.hom := rfl

end MathlibExtTest.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedProperImageOfFiniteAmplitude
