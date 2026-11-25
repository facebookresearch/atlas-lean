/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedProperImageModels
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Actual Ind inverse image and its exact derived localization

The compact generators are pulled back by the native ordinary sheaf
inverse image. They enter the original Ind category through restricted
Yoneda; the complete inverse image is its compact-Yoneda Kan extension.
The derived operator is the native localization of this fixed cochain
action. Its exactness input says exactly which cochain weak maps are
inverted. No freely selected inverse-image functor occurs.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2 and3.3;
Kashiwara--Schapira, Ind-sheaves. Native sheaf inverse image and
localization are Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679
(Apache2.0; Kim Morrison, Joël Riou and the Mathlib contributors).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafPushforwardModels

variable (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y)
  (S : OrdinaryIndSource k X)

/-- The native sheaf inverse image, on every compact source generator and map. -/
def inverseImageGenerators : CompactSheaf k Y ⥤ IndSheaf k X :=
  compactAsOrdinary k Y ⋙
    TopCat.Sheaf.pullback (ModuleCat.{0} k) f ⋙ ordinaryToInd k X S

/-- Construction input for this exact compact-generator inverse image. -/
structure IndInverseImageSource : Prop where
  hasKan : (Ind.yoneda (C := CompactSheaf k Y)).HasLeftKanExtension
    (inverseImageGenerators k f S)

/-- The actual inverse image is the native left Kan extension from compact sheaves. -/
def indInverseImage (D : IndInverseImageSource k f S) : IndSheaf k Y ⥤ IndSheaf k X :=
  letI := D.hasKan
  (Ind.yoneda (C := CompactSheaf k Y)).leftKanExtension
    (inverseImageGenerators k f S)

/-- The native generator unit fixes all ordinary inverse-image maps. -/
def inverseImageGeneratorUnit (D : IndInverseImageSource k f S) :
    inverseImageGenerators k f S ⟶ Ind.yoneda ⋙ indInverseImage k f S D :=
  letI := D.hasKan
  (Ind.yoneda (C := CompactSheaf k Y)).leftKanExtensionUnit
    (inverseImageGenerators k f S)

variable [CompactSheafSource k X] [CompactSheafSource k Y]

/-- Match native cochain zero morphisms with the abelian Ind structure used by Q. -/
local instance inverseAbelianPreadditive (Z : TopCat.{0}) [CompactSheafSource k Z] :
    Preadditive (IndSheaf k Z) := Abelian.toPreadditive

variable (D : IndInverseImageSource k f S) [(indInverseImage k f S D).Additive]
attribute [local instance] HasDerivedCategory.standard

/-- The actual cochain inverse image followed by the original target localization. -/
def inverseImageBeforeDeriving : CochainComplex (IndSheaf k Y) ℤ ⥤ IndDerived k X :=
  beforeRightDerivation (A := IndSheaf k Y) (B := IndSheaf k X) (indInverseImage k f S D)

/-- Exactness is a statement about every actual source quasi-isomorphism. -/
structure ExactIndInverseImageSource : Prop where
  inverts : (HomologicalComplex.quasiIso (IndSheaf k Y) (.up ℤ)).IsInvertedBy
    (inverseImageBeforeDeriving k f S D)

/-- The canonical exact derived inverse image of the prescribed Ind functor. -/
def derivedIndInverseImage (H : ExactIndInverseImageSource k f S D) :
    IndDerived k Y ⥤ IndDerived k X :=
  Localization.lift (inverseImageBeforeDeriving k f S D) H.inverts DerivedCategory.Q

/-- Its native localization comparison retains the actual cochain inverse-image action. -/
def derivedInverseImageComparison (H : ExactIndInverseImageSource k f S D) :
    DerivedCategory.Q ⋙ derivedIndInverseImage k f S D H ≅
      inverseImageBeforeDeriving k f S D :=
  Localization.fac (inverseImageBeforeDeriving k f S D) H.inverts DerivedCategory.Q

end MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
