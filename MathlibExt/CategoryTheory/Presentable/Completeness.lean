/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.DenseReflectivePresentation
public import MathlibExt.CategoryTheory.Limits.CreatedLimitFunctor
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Working-size completeness on the original locally presentable category

The original-category dense reflective right functor creates limits by the
native monadic construction. Genuine presheaf limits therefore lift to the
original coefficient category. The actual created cones, maps and comparison
are returned in addition to the completeness dictionary.

Original Hom-shaped products and cofree evaluation are obtained from these
limits. No original all-limit or all-product premise is used. Accessibility
of the power functors is a separate cardinal-bound result.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM uJ vJ uD vD

namespace CategoryTheory.Presentable.Completeness

open Limits Opposite

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]

/-- The actual original reflective right functor has native working-size creation data. -/
@[instance_reducible]
def createsLimits :
    CreatesLimitsOfSize.{w, w} (DenseReflectivePresentation.restrictedYoneda M κ) :=
  monadicCreatesLimits (DenseReflectivePresentation.restrictedYoneda M κ)

include κ in
/-- Genuine working-size limits are derived directly on the ORIGINAL coefficient category. -/
theorem hasLimitsOfSize : HasLimitsOfSize.{w, w} M :=
  hasLimits_of_reflective (DenseReflectivePresentation.restrictedYoneda M κ)

section Shapes

variable (J : Type uJ) [Category.{vJ} J] [EssentiallySmall.{w} J]

/-- The same actual creation data are transported along the genuine small-model equivalence. -/
@[instance_reducible]
def createsLimitsOfShape :
    CreatesLimitsOfShape J (DenseReflectivePresentation.restrictedYoneda M κ) := by
  letI := createsLimits M κ
  exact createsLimitsOfShapeOfEquiv (equivSmallModel.{w} J).symm
    (DenseReflectivePresentation.restrictedYoneda M κ)

/-- The actual target cones are the native limiting cones in the genuine presheaf category. -/
def targetCones (F : J ⥤ M) :
    Cone (F ⋙ DenseReflectivePresentation.restrictedYoneda M κ) := by
  letI : HasLimitsOfShape J ((DenseReflectivePresentation.index M κ)ᵒᵖ ⥤ Type w) :=
    hasLimitsOfShape_of_essentiallySmall J _
  exact limit.cone _

/-- The target universal properties come from genuine presheaf limits. -/
def targetLimits (F : J ⥤ M) : IsLimit (targetCones M κ J F) := by
  letI : HasLimitsOfShape J ((DenseReflectivePresentation.index M κ)ᵒᵖ ⥤ Type w) :=
    hasLimitsOfShape_of_essentiallySmall J _
  exact limit.isLimit _

/-- The selected original cone is created from that same actual target cone. -/
def cone (F : J ⥤ M) : Cone F :=
  CreatedLimitFunctor.cone (DenseReflectivePresentation.restrictedYoneda M κ)
    (createsLimitsOfShape M κ J) (targetCones M κ J) (targetLimits M κ J) F

/-- The same selected original cone is limiting by native creation. -/
def isLimit (F : J ⥤ M) : IsLimit (cone M κ J F) :=
  CreatedLimitFunctor.isLimit (DenseReflectivePresentation.restrictedYoneda M κ)
    (createsLimitsOfShape M κ J) (targetCones M κ J) (targetLimits M κ J) F

/-- The original created points and maps form the actual selected limit functor. -/
def limitFunctor : (J ⥤ M) ⥤ M :=
  CreatedLimitFunctor.functor (DenseReflectivePresentation.restrictedYoneda M κ)
    (createsLimitsOfShape M κ J) (targetCones M κ J) (targetLimits M κ J)

/-- The selected target points form their actual target limit functor. -/
def targetLimitFunctor : (J ⥤ M) ⥤ (DenseReflectivePresentation.index M κ)ᵒᵖ ⥤ Type w :=
  CreatedLimitFunctor.targetFunctor (DenseReflectivePresentation.restrictedYoneda M κ)
    (targetCones M κ J) (targetLimits M κ J)

/-- The complete natural comparison retains all original created and target points. -/
def comparison : limitFunctor M κ J ⋙ DenseReflectivePresentation.restrictedYoneda M κ ≅
    targetLimitFunctor M κ J :=
  CreatedLimitFunctor.comparison (DenseReflectivePresentation.restrictedYoneda M κ)
    (createsLimitsOfShape M κ J) (targetCones M κ J) (targetLimits M κ J)

/-- Every forward comparison component retains every original projection. -/
theorem comparison_hom_π (F : J ⥤ M) (j : J) :
    (comparison M κ J).hom.app F ≫ (targetCones M κ J F).π.app j =
      (DenseReflectivePresentation.restrictedYoneda M κ).map ((cone M κ J F).π.app j) :=
  CreatedLimitFunctor.pointIso_hom_π _ _ _ _ _ _

/-- Every inverse comparison component retains every original projection. -/
theorem comparison_inv_π (F : J ⥤ M) (j : J) :
    (comparison M κ J).inv.app F ≫
        (DenseReflectivePresentation.restrictedYoneda M κ).map ((cone M κ J F).π.app j) =
      (targetCones M κ J F).π.app j :=
  CreatedLimitFunctor.pointIso_inv_π _ _ _ _ _ _

/-- The whole original limit-map function satisfies all original projection equations. -/
theorem map_π {F G : J ⥤ M} (α : F ⟶ G) (j : J) :
    (limitFunctor M κ J).map α ≫ (cone M κ J G).π.app j =
      (cone M κ J F).π.app j ≫ α.app j :=
  CreatedLimitFunctor.map_π _ _ _ _ _ _

/-- The selected original universal lift retains the actual created cone. -/
def lift (F : J ⥤ M) (s : Cone F) : s.pt ⟶ (limitFunctor M κ J).obj F :=
  (isLimit M κ J F).lift s

/-- The selected original universal lift satisfies every original projection. -/
theorem lift_π (F : J ⥤ M) (s : Cone F) (j : J) :
    lift M κ J F s ≫ (cone M κ J F).π.app j = s.π.app j :=
  (isLimit M κ J F).fac s j

/-- The original universal lift is unique with those actual projection values. -/
theorem lift_unique (F : J ⥤ M) (s : Cone F)
    (m : s.pt ⟶ (limitFunctor M κ J).obj F)
    (hm : ∀ j, m ≫ (cone M κ J F).π.app j = s.π.app j) : m = lift M κ J F s :=
  (isLimit M κ J F).uniq s m hm

include κ in
/-- Every essentially working-small original index has genuine limits on original M. -/
theorem hasLimitsOfShape : HasLimitsOfShape J M where
  has_limit F := HasLimit.mk ⟨cone M κ J F, isLimit M κ J F⟩

end Shapes

section OriginalProducts

variable {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

include κ s in
/-- Every original Hom-shaped product exists by actual index local smallness
and the internally derived working-size coefficient limits. -/
theorem homProducts (d e : D) : HasProductsOfShape (d ⟶ e) M := by
  let : HasLimitsOfSize.{w, w} M := hasLimitsOfSize M κ
  let : LocallySmall.{w} D := locallySmall_of_faithful s.functor
  exact hasProductsOfShape_of_small (C := M) (d ⟶ e)

/-- The actual cofree functor is the native evaluation right adjoint,
using only the internally supplied original Hom products. -/
def cofree (d : D) : M ⥤ D ⥤ M := by
  letI (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  exact evaluationRightAdjoint M d

/-- The actual ordinary evaluation/cofree adjunction uses those same native values. -/
def evaluationCofreeAdjunction (d : D) :
    (evaluation D M).obj d ⊣ cofree M κ s d := by
  letI (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  exact evaluationAdjunctionLeft M d

/-- The cofree value is the product indexed by every ORIGINAL Hom label. -/
theorem cofree_obj (d e : D) (X : M) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    ((cofree M κ s d).obj X).obj e = ∏ᶜ fun _ : e ⟶ d ↦ X := rfl

/-- Every cofree index-action map has the actual original composition-indexed projection. -/
theorem cofree_map_π (d : D) {e e' : D} (a : e ⟶ e') (X : M) (g : e' ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    let _ : HasProductsOfShape (e' ⟶ d) M := homProducts M κ s e' d
    ((cofree M κ s d).obj X).map a ≫ Pi.π (fun _ : e' ⟶ d ↦ X) g =
      Pi.π (fun _ : e ⟶ d ↦ X) (a ≫ g) := by
  let (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  change (Pi.lift (fun g : e' ⟶ d ↦ Pi.π (fun _ : e ⟶ d ↦ X) (a ≫ g))) ≫
    Pi.π (fun _ : e' ⟶ d ↦ X) g = _
  exact Pi.lift_comp_π _ _

/-- Every coefficient map retains every actual original Hom-indexed projection. -/
theorem cofree_coefficient_map_π (d e : D) {X Y : M} (f : X ⟶ Y) (g : e ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    ((cofree M κ s d).map f).app e ≫ Pi.π (fun _ : e ⟶ d ↦ Y) g =
      Pi.π (fun _ : e ⟶ d ↦ X) g ≫ f := by
  let (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  change (Pi.lift (fun g : e ⟶ d ↦ Pi.π (fun _ : e ⟶ d ↦ X) g ≫ f)) ≫
    Pi.π (fun _ : e ⟶ d ↦ Y) g = _
  exact Pi.lift_comp_π _ _

/-- The original forward transpose retains the complete native component function. -/
theorem cofree_homEquiv_app (d e : D) (F : D ⥤ M) (X : M) (f : F.obj d ⟶ X) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    (((evaluationCofreeAdjunction M κ s d).homEquiv F X) f).app e =
      Pi.lift (fun g : e ⟶ d ↦ F.map g ≫ f) := by
  let (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  change (((evaluationAdjunctionLeft M d).homEquiv F X) f).app e = _
  rw [evaluationAdjunctionLeft, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The complete inverse transpose uses the ORIGINAL identity-indexed projection. -/
theorem cofree_homEquiv_symm (d : D) (F : D ⥤ M) (X : M)
    (α : F ⟶ (cofree M κ s d).obj X) :
    let _ : HasProductsOfShape (d ⟶ d) M := homProducts M κ s d d
    ((evaluationCofreeAdjunction M κ s d).homEquiv F X).symm α =
      α.app d ≫ Pi.π (fun _ : d ⟶ d ↦ X) (𝟙 d) := by
  let (e f : D) : HasProductsOfShape (e ⟶ f) M := homProducts M κ s e f
  let α' : F ⟶ (evaluationRightAdjoint M d).obj X := α
  change ((evaluationAdjunctionLeft M d).homEquiv F X).symm α' =
    α'.app d ≫ Pi.π (fun _ : d ⟶ d ↦ X) (𝟙 d)
  rw [evaluationAdjunctionLeft, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Each original Hom-power is the actual cofree functor followed by original evaluation. -/
def homPower (d e : D) : M ⥤ M := cofree M κ s d ⋙ (evaluation D M).obj e

/-- The Hom-power value retains all original Hom-indexed product labels. -/
theorem homPower_obj (d e : D) (X : M) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    (homPower M κ s d e).obj X = ∏ᶜ fun _ : e ⟶ d ↦ X := rfl

/-- The full Hom-power map retains the native original coefficient-map function. -/
theorem homPower_map (d e : D) {X Y : M} (f : X ⟶ Y) :
    let _ : HasProductsOfShape (e ⟶ d) M := homProducts M κ s e d
    (homPower M κ s d e).map f = Pi.lift (fun g : e ⟶ d ↦ Pi.π _ g ≫ f) := rfl

end OriginalProducts

end CategoryTheory.Presentable.Completeness

namespace CategoryTheory.Presentable

open Limits

/-- Actual local presentability supplies working-size completeness on the original category. -/
theorem hasLimitsOfSize_of_isLocallyPresentable (M : Type uM) [Category.{vM} M]
    [IsLocallyPresentable.{w} M] : HasLimitsOfSize.{w, w} M := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} M
  exact Completeness.hasLimitsOfSize M κ

end CategoryTheory.Presentable
