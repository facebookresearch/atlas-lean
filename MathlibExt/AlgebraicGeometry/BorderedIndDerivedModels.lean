/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedProperImageModels
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# The actual closed-boundary quotient of bounded ind-sheaves

The boundary category is the bounded derived category of the actual
closed complement. Its image uses the prescribed closed proper direct
image. The Verdier weak maps are exactly those with a boundary-image
cone. Localizing the full bounded source gives the bordered category.
Ordinary restriction and ind-stalk support are not used as the kernel:
they would erase nonzero ind-objects escaping towards the boundary.

Source: D'Agnolo--Kashiwara1311.2374v2, Definition3.2.6 and the
preceding counterexample in Section3. Native trW and localization are
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Joël Riou, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open BorderedRealSpaceModels CompactSupportIndSheaves IndSheafPushforwardModels

/-- The actual closed complement of the chosen open interior. -/
def boundarySpace (B : BorderedSpace) : TopCat.{0} :=
  TopCat.of {x : B.ambient | x ∉ B.openSet}

/-- Its native continuous inclusion into the original ambient space. -/
def boundaryInclusion (B : BorderedSpace) : boundarySpace B ⟶ B.ambient :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Boundary inclusion is proper as the inclusion of the actual closed complement. -/
theorem boundaryInclusion_proper (B : BorderedSpace) :
    IsProperMap (boundaryInclusion B) :=
  B.openSet.isOpen.isClosed_compl.isProperMap_subtypeVal

variable (k : Type) [Field k] (B : BorderedSpace)
  [CompactSheafSource k (boundarySpace B)] [CompactSheafSource k B.ambient]
  (P : CompactPushforwardSource k (boundaryInclusion B))
  (D : IndPushforwardSource k (boundaryInclusion B) P)

/-- Use the zero morphisms belonging to the same native abelian structure. -/
local instance boundaryAbelianPreadditive (Z : TopCat.{0}) [CompactSheafSource k Z] :
    Preadditive (IndSheaf k Z) := Abelian.toPreadditive

variable
  [(indProperImage k (boundaryInclusion B) P D).Additive]
  (H : DerivedIndPushforwardSource k (boundaryInclusion B) P D)

attribute [local instance] HasDerivedCategory.standard

/-- The null objects are actual images of bounded complexes on the closed boundary. -/
def boundaryImage : ObjectProperty (IndDerived k B.ambient) := fun K =>
  ∃ F : BoundedIndDerived k (boundarySpace B),
    Nonempty ((derivedIndProperImage k (boundaryInclusion B) P D H).obj F.obj ≅ K)

/-- A bounded-source morphism is inverted exactly when its native cone has that closed-boundary image. -/
def boundaryWeak : MorphismProperty (BoundedIndDerived k B.ambient) :=
  fun _ _ f => (boundaryImage k B P D H).trW f.hom

/-- The actual bordered bounded derived category is this canonical source localization. -/
abbrev BorderedDerived := (boundaryWeak k B P D H).Localization

/-- The quotient functor is the native localization functor of these exact weak maps. -/
def quotient : BoundedIndDerived k B.ambient ⥤ BorderedDerived k B P D H :=
  (boundaryWeak k B P D H).Q

end MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels
