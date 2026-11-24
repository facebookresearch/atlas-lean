/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedIndImageModels
public import MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels

/-!
# Normalized source data for the actual bounded Ind operations

These records collect only structural source proofs for already fixed
native operators. They contain no new object, carrier or functor.
The exposed operations are the same native tensor/localization and
compact-generator images, preserving their original objects and maps.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2,3.3--3.4 and4.1;
the exact native/source credits remain in the imported primitives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedIndOperationSources

open _root_.CategoryTheory
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafInverseImageModels
open IndSheafPushforwardModels BoundedIndImageModels IndSheafBoundedTensorModels

variable (k : Type) [Field k]

local instance operationAbelianPreadditive (X : TopCat.{0}) [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

section Tensor

variable (X : TopCat.{0}) [CompactSheafSource k X]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

/-- Source proofs for the original compact-generator tensor and native bounded localization. -/
structure TensorSource : Prop where
  compact : CompactTensorSource k X
  ind : IndTensorSource k X compact
  [cochain : TensorCochainSource k X compact ind]
  cohomology : BoundedCohomologySource k X
  localization : BoundedLocalizationSource k X cohomology
  bounded : BoundedTensorSource k X compact ind
  derived : DerivedTensorSource k X compact ind cohomology bounded

/-- The actual native bounded derived tensor determined by those structural source proofs. -/
def tensorFunctor (S : TensorSource k X) :
    BoundedIndDerived k X ⥤ BoundedIndDerived k X ⥤ BoundedIndDerived k X :=
  letI := S.cochain
  derivedTensor k X S.compact S.ind S.cohomology S.localization S.bounded S.derived

end Tensor

section Inverse

variable {X Y : TopCat.{0}} [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)

/-- Source proofs for the prescribed ordinary-generator inverse image on this actual map. -/
structure InverseSource : Prop where
  ordinary : OrdinaryIndSource k X
  ind : IndInverseImageSource k f ordinary
  [additive : (indInverseImage k f ordinary ind).Additive]
  exact : ExactIndInverseImageSource k f ordinary ind
  bounded : BoundedInverseImageSource k f ordinary ind exact

/-- The actual bounded inverse image constructed from those exact original generator proofs. -/
def inverseFunctor (S : InverseSource k f) : BoundedIndDerived k Y ⥤ BoundedIndDerived k X :=
  letI := S.additive
  boundedInverseImage k f S.ordinary S.ind S.exact S.bounded

end Inverse

section Proper

variable {X Y : TopCat.{0}} [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)

/-- Source proofs for the same actual compact-generator proper image and its boundedness. -/
structure ProperSource : Prop where
  compact : CompactPushforwardSource k f
  ind : IndPushforwardSource k f compact
  [additive : (indProperImage k f compact ind).Additive]
  derived : DerivedIndPushforwardSource k f compact ind
  bounded : BoundedProperImageSource k f compact ind derived

/-- The actual bounded proper image of that same prescribed compact-generator extension. -/
def properFunctor (S : ProperSource k f) : BoundedIndDerived k X ⥤ BoundedIndDerived k Y :=
  letI := S.additive
  boundedProperImage k f S.compact S.ind S.derived S.bounded

end Proper

end MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
