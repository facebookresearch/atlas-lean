/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDirectImage
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleAffinePresheafLeftExtension
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Sheaf inverse image on small étale sites

Sheafifying the affine presheaf left extension on the source scheme and
transporting through affine étale restriction on the target gives inverse
image. Its right adjoint is the site direct image.
Milne, *Lectures on Étale Cohomology*, §8, p. 60.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Continuity of the actual affine basis followed by arbitrary base change. -/
instance smallEtaleAffineBaseChangeIsContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleAffineBaseChange f).IsContinuous
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  exact Functor.isContinuous_comp (Scheme.AffineEtale.Spec Y) (smallEtaleBaseChange f)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

/-- Actual restriction of common-universe sheaves to the original affine basis. -/
def smallEtaleAffineRestriction (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} :=
  (Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology

/-- The original affine basis gives a genuine restriction equivalence,
using its stock hypercover density in the scheme universe. -/
instance smallEtaleAffineRestrictionIsEquivalence (Y : Scheme.{u}) :
    (smallEtaleAffineRestriction.{u, w} Y).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u}
    (Scheme.AffineEtale.Spec Y) (Scheme.AffineEtale.topology Y)
    Y.smallEtaleTopology AddCommGrpCat.{max u w}

/-- The fixed actual affine restriction equivalence, constructed internally. -/
def smallEtaleAffineRestrictionEquivalence (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ≌
      Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} :=
  (smallEtaleAffineRestriction.{u, w} Y).asEquivalence

/-- Sheafify the proved affine presheaf left Kan extension on the original
small étale site of the source scheme. -/
def smallEtaleAffineSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleAffineBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

/-- The affine construction has the actual affine direct image as right adjoint. -/
def smallEtaleAffineSheafAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleAffineSheafPullback.{u, w} f ⊣
      (smallEtaleAffineBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleAffineBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

/-- The actual original-site inverse-image functor, with the same affine Lan
and the fixed original affine restriction equivalence. -/
def smallEtaleInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleAffineRestrictionEquivalence.{u, w} Y).functor ⋙
    smallEtaleAffineSheafPullback.{u, w} f

/-- This is exactly the sheafification of the proved affine Lan of the actual
restriction of the original sheaf. -/
theorem smallEtaleInverseImage_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} f).obj Q =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        ((smallEtaleAffinePresheafLan.{u, w} f).obj
          (((smallEtaleAffineRestriction.{u, w} Y).obj Q).obj)) := by
  rfl

/-- Literal direct image followed by genuine affine restriction is the
pushforward belonging to that same affine-base-change functor. -/
def smallEtaleDirectImageAffineRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleAffineRestriction.{u, w} Y ≅
      (smallEtaleAffineBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  exact Functor.sheafPushforwardContinuousComp (Scheme.AffineEtale.Spec Y)
    (smallEtaleBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

/-- The transported right adjoint identifies with the same literal original
direct-image functor, using the actual affine restriction equivalence. -/
def smallEtaleInverseImageRightAdjointIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleAffineBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology ⋙
      (smallEtaleAffineRestrictionEquivalence.{u, w} Y).inverse ≅
      smallEtaleDirectImage.{u, max u w} f :=
  Functor.isoWhiskerRight (smallEtaleDirectImageAffineRestrictionIso.{u, w} f).symm
      (smallEtaleAffineRestrictionEquivalence.{u, w} Y).inverse ≪≫
    Functor.associator (smallEtaleDirectImage.{u, max u w} f)
      (smallEtaleAffineRestriction.{u, w} Y)
      (smallEtaleAffineRestrictionEquivalence.{u, w} Y).inverse ≪≫
    Functor.isoWhiskerLeft (smallEtaleDirectImage.{u, max u w} f)
      (smallEtaleAffineRestrictionEquivalence.{u, w} Y).unitIso.symm ≪≫
    Functor.rightUnitor (smallEtaleDirectImage.{u, max u w} f)

/-- The actual inverse image is left adjoint to the preceding literal direct image. -/
def smallEtaleInverseImageAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, w} f ⊣ smallEtaleDirectImage.{u, max u w} f :=
  ((smallEtaleAffineRestrictionEquivalence.{u, w} Y).toAdjunction.comp
      (smallEtaleAffineSheafAdjunction.{u, w} f)).ofNatIsoRight
    (smallEtaleInverseImageRightAdjointIso.{u, w} f)

/-- Additivity follows from the proved additivity of the same right adjoint. -/
theorem smallEtaleInverseImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleInverseImage.{u, w} f).Additive := by
  let : (smallEtaleDirectImage.{u, max u w} f).Additive :=
    smallEtaleDirectImage_additive.{u, max u w} f
  exact (smallEtaleInverseImageAdjunction.{u, w} f).left_adjoint_additive

/-- The natural additive Hom equivalence for every actual common-universe sheaf. -/
def smallEtaleInverseImageHomAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w})
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((smallEtaleInverseImage.{u, w} f).obj Q ⟶ R) ≃+
      (Q ⟶ (smallEtaleDirectImage.{u, max u w} f).obj R) := by
  let : (smallEtaleInverseImage.{u, w} f).Additive := smallEtaleInverseImage_additive.{u, w} f
  exact (smallEtaleInverseImageAdjunction.{u, w} f).homAddEquiv Q R

/-- The actual natural unit on all original common-universe sheaves. -/
def smallEtaleInverseImageUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) ⟶
      smallEtaleInverseImage.{u, w} f ⋙ smallEtaleDirectImage.{u, max u w} f :=
  (smallEtaleInverseImageAdjunction.{u, w} f).unit

/-- The actual natural counit on all original common-universe sheaves. -/
def smallEtaleInverseImageCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleInverseImage.{u, w} f ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  (smallEtaleInverseImageAdjunction.{u, w} f).counit

/-- The left triangle identity for every actual original common-universe sheaf. -/
theorem smallEtaleInverseImage_left_triangle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} f).map ((smallEtaleInverseImageUnit.{u, w} f).app Q) ≫
        (smallEtaleInverseImageCounit.{u, w} f).app ((smallEtaleInverseImage.{u, w} f).obj Q) =
      𝟙 ((smallEtaleInverseImage.{u, w} f).obj Q) := by
  exact (smallEtaleInverseImageAdjunction.{u, w} f).left_triangle_components Q

/-- The right triangle identity for every actual original common-universe sheaf. -/
theorem smallEtaleInverseImage_right_triangle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImageUnit.{u, w} f).app ((smallEtaleDirectImage.{u, max u w} f).obj R) ≫
        (smallEtaleDirectImage.{u, max u w} f).map ((smallEtaleInverseImageCounit.{u, w} f).app R) =
      𝟙 ((smallEtaleDirectImage.{u, max u w} f).obj R) := by
  exact (smallEtaleInverseImageAdjunction.{u, w} f).right_triangle_components R

/-- The construction applies to the canonical lift of every original smaller
coefficient sheaf, with no exactness assertion about that lift. -/
def smallEtaleInverseImageLiftHomAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((smallEtaleInverseImage.{u, w} f).obj ((liftCoefficients.{u, w} Y).obj Q) ⟶ R) ≃+
      ((liftCoefficients.{u, w} Y).obj Q ⟶ (smallEtaleDirectImage.{u, max u w} f).obj R) :=
  smallEtaleInverseImageHomAddEquiv.{u, w} f ((liftCoefficients.{u, w} Y).obj Q) R

/-- One fixed actual inverse-image construction has its literal associated
sheaf values and the additive adjunction to the same original direct image,
including both triangles and every original smaller-sheaf lift. -/
theorem original_small_etale_inverse_image_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let L := smallEtaleInverseImage.{u, w} f
    let D := smallEtaleDirectImage.{u, max u w} f
    L.Additive ∧
    (∀ Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w},
      L.obj Q = (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        ((smallEtaleAffinePresheafLan.{u, w} f).obj
          (((smallEtaleAffineRestriction.{u, w} Y).obj Q).obj))) ∧
    Nonempty (L ⊣ D) ∧
    (∀ (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w})
        (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}),
      Nonempty ((L.obj Q ⟶ R) ≃+ (Q ⟶ D.obj R))) ∧
    (∀ Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w},
      L.map ((smallEtaleInverseImageUnit.{u, w} f).app Q) ≫
          (smallEtaleInverseImageCounit.{u, w} f).app (L.obj Q) = 𝟙 (L.obj Q)) ∧
    (∀ R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w},
      (smallEtaleInverseImageUnit.{u, w} f).app (D.obj R) ≫
          D.map ((smallEtaleInverseImageCounit.{u, w} f).app R) = 𝟙 (D.obj R)) ∧
    ∀ (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
      (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}),
      Nonempty ((L.obj ((liftCoefficients.{u, w} Y).obj Q) ⟶ R) ≃+
        ((liftCoefficients.{u, w} Y).obj Q ⟶ D.obj R)) := by
  dsimp only
  exact ⟨smallEtaleInverseImage_additive.{u, w} f,
    (fun Q => smallEtaleInverseImage_obj.{u, w} f Q),
    ⟨smallEtaleInverseImageAdjunction.{u, w} f⟩,
    (fun Q R => ⟨smallEtaleInverseImageHomAddEquiv.{u, w} f Q R⟩),
    (fun Q => smallEtaleInverseImage_left_triangle.{u, w} f Q),
    (fun R => smallEtaleInverseImage_right_triangle.{u, w} f R),
    (fun Q R => ⟨smallEtaleInverseImageLiftHomAddEquiv.{u, w} f Q R⟩)⟩

end AlgebraicGeometry.Scheme.DerivedSections
