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
# Inverse image of abelian sheaves on small étale sites

Let `f : X → Y` be a scheme morphism and use additive-group coefficients in universe `max u
w`. Restriction from the small étale site of `Y` to its affine étale basis is an equivalence
of sheaf categories. Apply the affine base-change left extension and sheafify on `X` to
construct `f^*`.

Its right adjoint is direct image `f_*`. The additive Hom correspondence, unit, counit, and
both triangle identities are defined with these functors. The correspondence also applies to
coefficient sheaves lifted from universe `w`.

See Milne, Lectures on Étale Cohomology, §8, p. 60.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Affine étale base change is continuous.

Base change from the affine étale site of `Y` to the small étale site of `X` is continuous for
any scheme morphism `f : X → Y`. -/
instance smallEtaleAffineBaseChangeIsContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleAffineBaseChange f).IsContinuous
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  exact Functor.isContinuous_comp (Scheme.AffineEtale.Spec Y) (smallEtaleBaseChange f)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction of abelian sheaves to the affine étale basis.

Restrict common-universe abelian sheaves on `Y` along the affine étale basis functor. -/
def smallEtaleAffineRestriction (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} :=
  (Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology

/-- Affine étale restriction is an equivalence.

Restriction to the affine étale basis is an equivalence of the corresponding abelian-sheaf
categories. -/
instance smallEtaleAffineRestrictionIsEquivalence (Y : Scheme.{u}) :
    (smallEtaleAffineRestriction.{u, w} Y).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u}
    (Scheme.AffineEtale.Spec Y) (Scheme.AffineEtale.topology Y)
    Y.smallEtaleTopology AddCommGrpCat.{max u w}

/-- Equivalence between full and affine étale sheaf categories.

Bundle affine étale restriction and its inverse as a categorical equivalence. -/
def smallEtaleAffineRestrictionEquivalence (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ≌
      Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} :=
  (smallEtaleAffineRestriction.{u, w} Y).asEquivalence

/-- Sheaf pullback from the affine étale basis.

Apply left extension along affine base change and sheafification to obtain a functor from
affine étale sheaves on `Y` to small étale sheaves on `X`. -/
def smallEtaleAffineSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleAffineBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

/-- Affine sheaf pullback is left adjoint to affine direct image.

The affine sheaf pullback construction is left adjoint to continuous sheaf pushforward along
affine base change. -/
def smallEtaleAffineSheafAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleAffineSheafPullback.{u, w} f ⊣
      (smallEtaleAffineBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleAffineBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

/-- Inverse image through affine restriction and sheafification.

Compose affine étale restriction on `Y` with affine sheaf pullback to define `f^*` on common-
universe abelian sheaves. -/
def smallEtaleInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleAffineRestrictionEquivalence.{u, w} Y).functor ⋙
    smallEtaleAffineSheafPullback.{u, w} f

/-- Inverse image sheaf as the sheafified affine left extension.

The inverse image of `Q` is the sheafification on `X` of the affine presheaf left extension of
its affine restriction. -/
theorem smallEtaleInverseImage_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} f).obj Q =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        ((smallEtaleAffinePresheafLan.{u, w} f).obj
          (((smallEtaleAffineRestriction.{u, w} Y).obj Q).obj)) := by
  rfl

/-- Direct image restriction agrees with affine pushforward.

Direct image on the full small étale site followed by affine restriction is naturally
isomorphic to continuous pushforward along affine base change. -/
def smallEtaleDirectImageAffineRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleAffineRestriction.{u, w} Y ≅
      (smallEtaleAffineBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  exact Functor.sheafPushforwardContinuousComp (Scheme.AffineEtale.Spec Y)
    (smallEtaleBaseChange f) AddCommGrpCat.{max u w}
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

/-- The affine construction right adjoint is direct image.

Affine pushforward followed by inverse affine restriction is naturally isomorphic to the full-
site direct-image functor. -/
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

/-- Small étale inverse image is left adjoint to direct image.

The affine construction and restriction equivalence give `f^* ⊣ f_*` on abelian sheaves with
common-universe coefficients. -/
def smallEtaleInverseImageAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, w} f ⊣ smallEtaleDirectImage.{u, max u w} f :=
  ((smallEtaleAffineRestrictionEquivalence.{u, w} Y).toAdjunction.comp
      (smallEtaleAffineSheafAdjunction.{u, w} f)).ofNatIsoRight
    (smallEtaleInverseImageRightAdjointIso.{u, w} f)

/-- Small étale inverse image is additive.

Inverse image preserves sums of abelian-sheaf morphisms. -/
theorem smallEtaleInverseImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleInverseImage.{u, w} f).Additive := by
  let : (smallEtaleDirectImage.{u, max u w} f).Additive :=
    smallEtaleDirectImage_additive.{u, max u w} f
  exact (smallEtaleInverseImageAdjunction.{u, w} f).left_adjoint_additive

/-- Additive correspondence for the inverse image adjunction.

There is an additive equivalence between sheaf maps `f^*Q → R` on `X` and sheaf maps `Q →
f_*R` on `Y`. -/
def smallEtaleInverseImageHomAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w})
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((smallEtaleInverseImage.{u, w} f).obj Q ⟶ R) ≃+
      (Q ⟶ (smallEtaleDirectImage.{u, max u w} f).obj R) := by
  let : (smallEtaleInverseImage.{u, w} f).Additive := smallEtaleInverseImage_additive.{u, w} f
  exact (smallEtaleInverseImageAdjunction.{u, w} f).homAddEquiv Q R

/-- Unit of small étale inverse image and direct image.

The adjunction gives the natural map `Q → f_*f^*Q` on sheaves over `Y`. -/
def smallEtaleInverseImageUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) ⟶
      smallEtaleInverseImage.{u, w} f ⋙ smallEtaleDirectImage.{u, max u w} f :=
  (smallEtaleInverseImageAdjunction.{u, w} f).unit

/-- Counit of small étale inverse image and direct image.

The adjunction gives the natural map `f^*f_*R → R` on sheaves over `X`. -/
def smallEtaleInverseImageCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleInverseImage.{u, w} f ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  (smallEtaleInverseImageAdjunction.{u, w} f).counit

/-- Inverse image unit and counit satisfy the left triangle.

Apply inverse image to the unit at `Q` and then the counit at `f^*Q`; the composite is the
identity. -/
theorem smallEtaleInverseImage_left_triangle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImage.{u, w} f).map ((smallEtaleInverseImageUnit.{u, w} f).app Q) ≫
        (smallEtaleInverseImageCounit.{u, w} f).app ((smallEtaleInverseImage.{u, w} f).obj Q) =
      𝟙 ((smallEtaleInverseImage.{u, w} f).obj Q) := by
  exact (smallEtaleInverseImageAdjunction.{u, w} f).left_triangle_components Q

/-- Inverse image unit and counit satisfy the right triangle.

The unit at `f_*R`, followed by direct image of the counit at `R`, is the identity on `f_*R`. -/
theorem smallEtaleInverseImage_right_triangle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleInverseImageUnit.{u, w} f).app ((smallEtaleDirectImage.{u, max u w} f).obj R) ≫
        (smallEtaleDirectImage.{u, max u w} f).map ((smallEtaleInverseImageCounit.{u, w} f).app R) =
      𝟙 ((smallEtaleDirectImage.{u, max u w} f).obj R) := by
  exact (smallEtaleInverseImageAdjunction.{u, w} f).right_triangle_components R

/-- Inverse image adjunction for lifted source coefficients.

For a sheaf in coefficient universe `w`, lift it to `max u w` and apply the additive
adjunction correspondence with a target sheaf on `X`. -/
def smallEtaleInverseImageLiftHomAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    ((smallEtaleInverseImage.{u, w} f).obj ((liftCoefficients.{u, w} Y).obj Q) ⟶ R) ≃+
      ((liftCoefficients.{u, w} Y).obj Q ⟶ (smallEtaleDirectImage.{u, max u w} f).obj R) :=
  smallEtaleInverseImageHomAddEquiv.{u, w} f ((liftCoefficients.{u, w} Y).obj Q) R

/-- Inverse image construction and adjunction identities.

Inverse image is additive, has the affine-left-extension sheafification formula, is left
adjoint to direct image with additive Hom correspondences, and satisfies both triangle
identities, including the correspondence for lifted source coefficients. -/
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
