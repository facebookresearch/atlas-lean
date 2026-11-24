/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedProperImageModels

/-!
# The same actual Ind images on the bounded derived carriers

Every object and morphism is the original native derived image.
Boundedness inputs refer only to that fixed operator. They supply the
full-subcategory lift needed by graph kernels and convolution, without
introducing a separately chosen bounded functor. Proper-image
boundedness is kept explicit; it is not asserted for arbitrary maps.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections3.3--3.4;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedIndImageModels

open _root_.CategoryTheory
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafInverseImageModels
open IndSheafPushforwardModels

variable (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y)
  [CompactSheafSource k X] [CompactSheafSource k Y]

local instance boundedImageAbelianPreadditive (Z : TopCat.{0}) [CompactSheafSource k Z] :
    Preadditive (IndSheaf k Z) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

section Inverse

variable (S : OrdinaryIndSource k X) (D : IndInverseImageSource k f S)
  [(indInverseImage k f S D).Additive] (E : ExactIndInverseImageSource k f S D)

/-- The boundedness statement refers to the same native exact derived inverse image. -/
structure BoundedInverseImageSource : Prop where
  bounded : ∀ K : BoundedIndDerived k Y,
    IsBounded k X ((derivedIndInverseImage k f S D E).obj K.obj)

/-- The actual exact inverse image on the original full bounded derived categories. -/
def boundedInverseImage (H : BoundedInverseImageSource k f S D E) :
    BoundedIndDerived k Y ⥤ BoundedIndDerived k X where
  obj K := ⟨(derivedIndInverseImage k f S D E).obj K.obj, H.bounded K⟩
  map a := ObjectProperty.homMk ((derivedIndInverseImage k f S D E).map a.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact (derivedIndInverseImage k f S D E).map_id K.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (derivedIndInverseImage k f S D E).map_comp a.hom b.hom

end Inverse

section Proper

variable (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
  [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)

/-- The finite-amplitude condition is measured by actual homology of images of all original degree-zero Ind objects. -/
def FiniteProperImageAmplitude : Prop :=
  ∃ a b : ℤ, ∀ (K : IndSheaf k X) (n : ℤ), n < a ∨ b < n →
    Limits.IsZero ((DerivedCategory.homologyFunctor (IndSheaf k Y) n).obj
      ((derivedIndProperImage k f P D E).obj ((DerivedCategory.singleFunctor (IndSheaf k X) 0).obj K)))

/-- Proper-image boundedness concerns every original bounded complex under the same derived proper image. -/
structure BoundedProperImageSource : Prop where
  bounded : ∀ K : BoundedIndDerived k X,
    IsBounded k Y ((derivedIndProperImage k f P D E).obj K.obj)

/-- The actual proper image on full bounded derived categories, when its structural boundedness is known. -/
def boundedProperImage (H : BoundedProperImageSource k f P D E) :
    BoundedIndDerived k X ⥤ BoundedIndDerived k Y where
  obj K := ⟨(derivedIndProperImage k f P D E).obj K.obj, H.bounded K⟩
  map a := ObjectProperty.homMk ((derivedIndProperImage k f P D E).map a.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact (derivedIndProperImage k f P D E).map_id K.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (derivedIndProperImage k f P D E).map_comp a.hom b.hom

end Proper

end MathlibExt.AlgebraicGeometry.BoundedIndImageModels
