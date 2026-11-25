/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeSmallObjectPresentation

/-! # Whole original native factor, Arrow/Under retract and base-cofibration owner -/

@[expose] public section

noncomputable section

universe w v u

namespace MathlibExtTest.CategoryTheory.SmallObject.NativeSmallObjectPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty HomotopicalAlgebra
open _root_.CategoryTheory.SmallObject.NativeSmallObjectPresentation

variable {C : Type u} [Category.{v} C]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [I.IsCardinalForSmallObjectArgument κ]

theorem originalNativeEndpoint {X Y : C} (f : X ⟶ Y) :
    (nativeTree I κ f).endpointObj = Under.mk (CategoryTheory.SmallObject.ιObj I κ f) := rfl

theorem originalNativeRoot {X Y : C} (f : X ⟶ Y) :
    (nativeTree I κ f).hom = CategoryTheory.SmallObject.ιObj I κ f := rfl

theorem originalNativeFactor {X Y : C} (f : X ⟶ Y) :
    (nativeTree I κ f).hom ≫ CategoryTheory.SmallObject.πObj I κ f = f := CategoryTheory.SmallObject.ιObj_πObj I κ f

theorem allOriginalNativeLabels {X Y : C} (f : X ⟶ Y)
    (a : (CategoryTheory.SmallObject.relativeCellComplexιObj I κ f).Cells) :
    (nativeTree I κ f).label a = a.i := rfl

theorem allOriginalNativeLabelMembers {X Y : C} (f : X ⟶ Y)
    (a : (CategoryTheory.SmallObject.relativeCellComplexιObj I κ f).Cells) :
    I ((generatorArrows I) ((nativeTree I κ f).label a)).hom := nativeTree_cell_mem I κ f a

theorem everyOriginalNativeCellInclusion {X Y : C} (f : X ⟶ Y)
    (a : (CategoryTheory.SmallObject.relativeCellComplexιObj I κ f).Cells) :
    (nativeTree I κ f).cell a ≫ ((nativeTree I κ f).inclusion a).right = a.ι :=
  nativeTree_cell_inclusion I κ f a

theorem originalNativePresentationSource {X Y : C} (f : X ⟶ Y) :
    (nativePresentation I κ f).arrowIso.hom.left = 𝟙 X := rfl

theorem originalNativePresentationTarget {X Y : C} (f : X ⟶ Y) :
    (nativePresentation I κ f).arrowIso.hom.right = 𝟙 (CategoryTheory.SmallObject.obj I κ f) := rfl

theorem allOriginalMiddleMapFunctions :
    (fun (f g : Arrow C) (φ : f ⟶ g) => (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map φ) =
      (fun (f g : Arrow C) (φ : f ⟶ g) => CategoryTheory.SmallObject.objMap I κ φ) := rfl

theorem originalMiddleIdentity (f : Arrow C) :
    (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map (𝟙 f) = 𝟙 ((nativeTree I κ f.hom).endpointObj.right) :=
  (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map_id f

theorem originalMiddleComposition {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map (φ ≫ ψ) =
      (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map φ ≫ (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map ψ :=
  (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map_comp φ ψ

theorem originalRootNaturality {f g : Arrow C} (φ : f ⟶ g) :
    (nativeTree I κ f.hom).hom ≫ (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map φ =
      φ.left ≫ (nativeTree I κ g.hom).hom := CategoryTheory.SmallObject.ιObj_naturality I κ φ

theorem originalRightNaturality {f g : Arrow C} (φ : f ⟶ g) :
    (CategoryTheory.SmallObject.functorialFactorizationData I κ).Z.map φ ≫ CategoryTheory.SmallObject.πObj I κ g.hom =
      CategoryTheory.SmallObject.πObj I κ f.hom ≫ φ.right :=
  CategoryTheory.SmallObject.πObj_naturality I κ φ

theorem originalCanonicalLiftValue {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    retractLift I κ f hf =
      letI : HasLiftingProperty f (CategoryTheory.SmallObject.πObj I κ f) :=
        hf _ (CategoryTheory.SmallObject.rlp_πObj I κ f)
      (retractSquare I κ f).lift := rfl

theorem originalLiftLeft {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    f ≫ retractLift I κ f hf = (nativeTree I κ f).hom := retractLift_left I κ f hf

theorem originalLiftRight {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    retractLift I κ f hf ≫ CategoryTheory.SmallObject.πObj I κ f = 𝟙 Y :=
  retractLift_right I κ f hf

theorem originalUnderRetraction {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (underRetract I κ f hf).i ≫ (underRetract I κ f hf).r = 𝟙 (Under.mk f) :=
  (underRetract I κ f hf).retract

theorem originalArrowRetraction {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (arrowRetract I κ f hf).i ≫ (arrowRetract I κ f hf).r = 𝟙 (Arrow.mk f) :=
  (arrowRetract I κ f hf).retract

theorem originalArrowSourceForward {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (arrowRetract I κ f hf).i.left = 𝟙 X := rfl

theorem originalArrowSourceBackward {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (arrowRetract I κ f hf).r.left = 𝟙 X := rfl

theorem originalArrowTargetForward {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (arrowRetract I κ f hf).i.right = retractLift I κ f hf := rfl

theorem originalArrowTargetBackward {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (arrowRetract I κ f hf).r.right = CategoryTheory.SmallObject.πObj I κ f := rfl

theorem originalProducedIdempotent {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    endpointIdempotent I κ f hf ≫ endpointIdempotent I κ f hf =
      endpointIdempotent I κ f hf := endpointIdempotent_comp I κ f hf

theorem originalProducedIdempotentRoot {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (nativeTree I κ f).hom ≫ (endpointIdempotent I κ f hf).right = (nativeTree I κ f).hom :=
  Under.w (endpointIdempotent I κ f hf)

end MathlibExtTest.CategoryTheory.SmallObject.NativeSmallObjectPresentation

namespace MathlibExtTest.CategoryTheory.SmallObject.NativeSmallObjectPresentation.Base

open _root_.CategoryTheory _root_.CategoryTheory.MorphismProperty HomotopicalAlgebra
open _root_.CategoryTheory.SmallObject.NativeSmallObjectPresentation
open HomotopicalAlgebra.CofibrantGenerationData

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The original base cofibration uses its own native under-root retract data. -/
def actualOriginalCofibrationUnder {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    Retract (Under.mk f) (nativeTree d.I κ f).endpointObj :=
  d.originalCofibrationUnderRetract f hf

/-- The original base cofibration uses its own identity-on-source Arrow retract. -/
def actualOriginalCofibrationArrow {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    RetractArrow f (nativeTree d.I κ f).hom :=
  d.originalCofibrationArrowRetract f hf

theorem actualOriginalSourceForward {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (actualOriginalCofibrationArrow d f hf).i.left = 𝟙 X := rfl

theorem actualOriginalSourceBackward {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (actualOriginalCofibrationArrow d f hf).r.left = 𝟙 X := rfl

theorem sameOriginalMiddleObject {X Y : C} (f : X ⟶ Y) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (nativeTree d.I κ f).endpointObj.right = d.cofibrantFactorizationData.Z.obj (Arrow.mk f) := rfl

theorem sameOriginalRightFactor {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (actualOriginalCofibrationArrow d f hf).r.right =
      d.cofibrantFactorizationData.p.app (Arrow.mk f) := rfl

end MathlibExtTest.CategoryTheory.SmallObject.NativeSmallObjectPresentation.Base
