/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels
public import MathlibExt.AlgebraicGeometry.BoundedIndOperationSources

/-!
# Ringed images on the actual Ind coefficient geometry

The source rings are the actual inverse mapMon images of the target
ring. The underived proper image has the prescribed compact-Yoneda
coefficient functor and both original projection-mate actions. Its
derived image is native total right derivation. Exceptional inverse image
is that exact functor's native right adjoint. This is the graph i! and
closed-boundary image used by enhanced D modules.

Source: DK1311.2374v2 Sections3.3,4.10,8.2;
Mathlib56a005 native Ind/Kan/projection-mates/derivation, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeRingedIndImageModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open BoundedIndOperationSources IndSheafPushforwardModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeMappedUnitMonoids

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CompactSheafSource ℂ Y]
  [IndSpaceSource X] [IndSpaceSource Y]
  (I : InverseMonoidalSource f) (P : ProperSource ℂ f)

local instance imageInverseBraided : (originalInverse f I).Braided := I.braided

def originalProper : IndSheaf ℂ Y ⥤ IndSheaf ℂ X :=
  indProperImage ℂ f P.compact P.ind

variable (adj : originalInverse f I ⊣ originalProper f P) (R : Mon (IndSheaf ℂ X))

structure RingedIndImageSource where
  actual : RingedImageSource (originalInverse f I) (originalProper f P) adj
    (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y)) R (Mon.trivial (IndSheaf ℂ X))
    (Iso.refl _) (mappedUnitIso (originalInverse f I))

variable (S : RingedIndImageSource f I P adj R)

def originalRingedProper : Bimod (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y)) ⥤
    Bimod R (Mon.trivial (IndSheaf ℂ X)) := S.actual.functor

local instance imageModulePreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z]
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [IndSpaceSource Z] (A B : Mon (IndSheaf ℂ Z)) : Preadditive (Bimod A B) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable [(originalRingedProper f I P adj R S).Additive]
  (D : RightDerivationSource (originalRingedProper f I P adj R S))

def derivedRingedProper :
    DerivedCategory (Bimod (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y))) ⥤
      DerivedCategory (Bimod R (Mon.trivial (IndSheaf ℂ X))) :=
  derivedImage (originalRingedProper f I P adj R S) D

variable [(derivedRingedProper f I P adj R S D).IsLeftAdjoint]

def ringedExceptional : DerivedCategory (Bimod R (Mon.trivial (IndSheaf ℂ X))) ⥤
    DerivedCategory (Bimod (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y))) :=
  (derivedRingedProper f I P adj R S D).rightAdjoint

end MathlibExt.AlgebraicGeometry.NativeRingedIndImageModels
