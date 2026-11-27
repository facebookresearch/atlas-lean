/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Ringed enhanced quotient from the original boundary and projection images

The null generators are the image of the actual boundary proper image
and the actual pi-inverse image, in the original native module category.
Their isomorphism closed triangulated envelope defines the quotient.
Coefficient forgetting is localized from the actual underlying functor;
both representatives are native adjoints of that exact quotient.

Source: DK1311.2374v2 Definitions4.10.1,4.10.4 and Section4.4;
Mathlib56a005 native trW, localization and adjoints, Joël Riou, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open NativeBoundedBimoduleModels

universe u v uB uP vB vP uE vE
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [∀ R S : Mon C, Abelian (Bimod R S)] (R S : Mon C)

local instance enhancedModulePreadditive : Preadditive (Bimod R S) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable {Boundary : Type uB} [Category.{vB} Boundary]
  {Base : Type uP} [Category.{vP} Base]
  (closedBoundaryImage : Boundary ⥤ BoundedModules R S)
  (piInverseImage : Base ⥤ BoundedModules R S)

def moduleNullGenerators : ObjectProperty (DerivedCategory (Bimod R S)) := fun K =>
  (∃ F : Boundary, Nonempty ((closedBoundaryImage.obj F).obj ≅ K)) ∨
    ∃ F : Base, Nonempty ((piInverseImage.obj F).obj ≅ K)

def moduleNullEnvelope : ObjectProperty (DerivedCategory (Bimod R S)) := fun K =>
  ∀ P : ObjectProperty (DerivedCategory (Bimod R S)),
    P.IsTriangulated → P.IsClosedUnderIsomorphisms →
      moduleNullGenerators R S closedBoundaryImage piInverseImage ≤ P → P K

def moduleWeak : MorphismProperty (BoundedModules R S) :=
  fun _ _ f => (moduleNullEnvelope R S closedBoundaryImage piInverseImage).trW f.hom

abbrev EnhancedModules := (moduleWeak R S closedBoundaryImage piInverseImage).Localization

abbrev moduleQuotient : BoundedModules R S ⥤
    EnhancedModules R S closedBoundaryImage piInverseImage :=
  (moduleWeak R S closedBoundaryImage piInverseImage).Q

structure ModuleRepresentativeSource : Prop where
  left : (moduleQuotient R S closedBoundaryImage piInverseImage).IsRightAdjoint
  right : (moduleQuotient R S closedBoundaryImage piInverseImage).IsLeftAdjoint

def moduleLeftRepresentative
    (L : ModuleRepresentativeSource R S closedBoundaryImage piInverseImage) :
    EnhancedModules R S closedBoundaryImage piInverseImage ⥤ BoundedModules R S :=
  letI := L.left
  (moduleQuotient R S closedBoundaryImage piInverseImage).leftAdjoint

def moduleRightRepresentative
    (L : ModuleRepresentativeSource R S closedBoundaryImage piInverseImage) :
    EnhancedModules R S closedBoundaryImage piInverseImage ⥤ BoundedModules R S :=
  letI := L.right
  (moduleQuotient R S closedBoundaryImage piInverseImage).rightAdjoint

def moduleRightAdjunction (L : ModuleRepresentativeSource R S closedBoundaryImage piInverseImage) :
    moduleQuotient R S closedBoundaryImage piInverseImage ⊣
      moduleRightRepresentative R S closedBoundaryImage piInverseImage L :=
  letI := L.right
  Adjunction.ofIsLeftAdjoint (moduleQuotient R S closedBoundaryImage piInverseImage)

variable {E : Type uE} [Category.{vE} E] (underlying : BoundedModules R S ⥤ E)

structure ModuleCoefficientQuotientSource : Prop where
  inverts : (moduleWeak R S closedBoundaryImage piInverseImage).IsInvertedBy underlying

def enhancedModuleCoefficients
    (F : ModuleCoefficientQuotientSource R S closedBoundaryImage piInverseImage underlying) :
    EnhancedModules R S closedBoundaryImage piInverseImage ⥤ E :=
  Localization.lift underlying F.inverts
    (moduleQuotient R S closedBoundaryImage piInverseImage)

end MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients
