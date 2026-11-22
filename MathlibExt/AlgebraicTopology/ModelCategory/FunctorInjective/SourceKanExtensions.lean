/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceConstruction
import MathlibExt.CategoryTheory.Functor.KanExtension.EssentialIndexBounds
import MathlibExt.CategoryTheory.Presentable.Completeness

/-!
# Native right Kan extensions from original combinatorial sources

The actual coefficient presentability and the complete original index
equivalences derive the original comma limits and native right Kan existence.
The returned Ran functor and adjunction are the existing native choices;
their maps, units, counits and limit comparisons retain the original objects
and natural transformations. Two independent coefficient generating ranks
may construct the two injective models.

This is *Higher Topos Theory*, author version April 9, 2017, Proposition
A.2.8.7(2), printed page 833 (PDF page 851), through actual essentially small
original indices. No target Kan, model or Quillen outcome is a caller premise.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uE vE uC vC

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace HomotopicalAlgebra.FunctorInjective.SourceKanExtensions

namespace FromData

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (c : SourceConstruction.CoefficientData.{w} C)
  (sD : EssentialIndexData.{w} D C) (sE : EssentialIndexData.{w} E C) (u : D ⥤ E)

include c sD sE

/-- Every ORIGINAL right comma shape has its actual coefficient limits.
The complete comma bounds and coefficient completeness are both derived. -/
theorem hasCommaLimits (e : E) : HasLimitsOfShape (StructuredArrow e u) C := by
  let : Fact c.cardinal.IsRegular := c.regular
  let : IsCardinalLocallyPresentable C c.cardinal := c.locallyPresentable
  let : EssentiallySmall.{w} (StructuredArrow e u) :=
    sD.structuredArrow_essentiallySmall sE u e
  exact CategoryTheory.Presentable.Completeness.hasLimitsOfShape C c.cardinal
    (StructuredArrow e u)

/-- Pointwise native right Kan existence uses the unchanged original comma diagrams. -/
theorem hasPointwiseRightKanExtension (F : D ⥤ C) : u.HasPointwiseRightKanExtension F := by
  intro e
  let : HasLimitsOfShape (StructuredArrow e u) C := hasCommaLimits c sD sE u e
  infer_instance

/-- The complete native right Kan witness is constructed for every original functor. -/
theorem hasRightKanExtension (F : D ⥤ C) : u.HasRightKanExtension F := by
  let : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
  infer_instance

/-- Return the native Ran functor using only the constructed source witnesses. -/
def ran : (D ⥤ C) ⥤ (E ⥤ C) := by
  let (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension c sD sE u F
  exact u.ran

/-- The actual native restriction/Ran adjunction is constructed on the original categories. -/
def adjunction : (whiskeringLeft D E C).obj u ⊣ ran c sD sE u := by
  let (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension c sD sE u F
  exact u.ranAdjunction C

/-- The whole original Ran object/map functor is unchanged, with the same native choice. -/
theorem ran_eq_native :
    letI (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension c sD sE u F
    ran c sD sE u = u.ran := rfl

/-- Both whole unit/counit transformations and the native adjunct function are retained. -/
theorem adjunction_eq_native :
    letI (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension c sD sE u F
    adjunction c sD sE u = u.ranAdjunction C := rfl

/-- Every original input natural transformation keeps its entire native Ran map. -/
theorem ran_map {F G : D ⥤ C} (α : F ⟶ G) :
    letI (X : D ⥤ C) : u.HasRightKanExtension X := hasRightKanExtension c sD sE u X
    (ran c sD sE u).map α = u.ran.map α := rfl

/-- The native value compares to the limit of the ORIGINAL comma diagram. -/
def evaluationIso (F : D ⥤ C) (e : E) :
    letI : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
    ((ran c sD sE u).obj F).obj e ≅ limit (StructuredArrow.proj e u ⋙ F) := by
  let (X : D ⥤ C) : u.HasRightKanExtension X := hasRightKanExtension c sD sE u X
  let : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
  exact u.ranObjObjIsoLimit F e

/-- The forward limit comparison retains every original comma arrow and counit leg. -/
theorem evaluationIso_hom_projection (F : D ⥤ C) (e : E) (a : StructuredArrow e u) :
    letI : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
    (evaluationIso c sD sE u F e).hom ≫ limit.π (StructuredArrow.proj e u ⋙ F) a =
      ((ran c sD sE u).obj F).map a.hom ≫
        ((adjunction c sD sE u).counit.app F).app a.right := by
  let (X : D ⥤ C) : u.HasRightKanExtension X := hasRightKanExtension c sD sE u X
  let : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
  change (u.ranObjObjIsoLimit F e).hom ≫ limit.π _ a =
    (u.ran.obj F).map a.hom ≫ ((u.ranAdjunction C).counit.app F).app a.right
  rw [Functor.ranAdjunction_counit]
  exact u.ranObjObjIsoLimit_hom_π F e a

/-- The inverse comparison preserves those same complete original projection maps. -/
theorem evaluationIso_inv_projection (F : D ⥤ C) (e : E) (a : StructuredArrow e u) :
    letI : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
    (evaluationIso c sD sE u F e).inv ≫ ((ran c sD sE u).obj F).map a.hom ≫
        ((adjunction c sD sE u).counit.app F).app a.right =
      limit.π (StructuredArrow.proj e u ⋙ F) a := by
  let (X : D ⥤ C) : u.HasRightKanExtension X := hasRightKanExtension c sD sE u X
  let : u.HasPointwiseRightKanExtension F := hasPointwiseRightKanExtension c sD sE u F
  change (u.ranObjObjIsoLimit F e).inv ≫ (u.ran.obj F).map a.hom ≫
    ((u.ranAdjunction C).counit.app F).app a.right = limit.π _ a
  rw [Functor.ranAdjunction_counit]
  exact u.ranObjObjIsoLimit_inv_π F e a

/-- The original whole unit is natural on every original target-index transformation. -/
theorem unit_naturality {F G : E ⥤ C} (α : F ⟶ G) :
    α ≫ (adjunction c sD sE u).unit.app G =
      (adjunction c sD sE u).unit.app F ≫
        (ran c sD sE u).map (((whiskeringLeft D E C).obj u).map α) :=
  (adjunction c sD sE u).unit.naturality α

/-- The whole counit retains naturality in every original source transformation. -/
theorem counit_naturality {F G : D ⥤ C} (α : F ⟶ G) :
    ((whiskeringLeft D E C).obj u).map ((ran c sD sE u).map α) ≫
        (adjunction c sD sE u).counit.app G =
      (adjunction c sD sE u).counit.app F ≫ α :=
  (adjunction c sD sE u).counit.naturality α

/-- The original restriction-side triangle uses the same entire unit and counit. -/
theorem left_triangle (F : E ⥤ C) :
    ((whiskeringLeft D E C).obj u).map ((adjunction c sD sE u).unit.app F) ≫
      (adjunction c sD sE u).counit.app (((whiskeringLeft D E C).obj u).obj F) = 𝟙 _ :=
  (adjunction c sD sE u).left_triangle_components F

/-- The original Ran-side triangle is an equality of whole natural transformations. -/
theorem right_triangle (F : D ⥤ C) :
    (adjunction c sD sE u).unit.app ((ran c sD sE u).obj F) ≫
      (ran c sD sE u).map ((adjunction c sD sE u).counit.app F) = 𝟙 _ :=
  (adjunction c sD sE u).right_triangle_components F

/-- Independent actual coefficient ranks construct the two models, and the
same native adjunction is Quillen by their proved pointwise left classes. -/
theorem isQuillen (cE : SourceConstruction.CoefficientData.{w'} C)
    (tE : EssentialIndexData.{w'} E C) :
    letI : ModelCategory (E ⥤ C) := cE.modelCategory tE
    letI : ModelCategory (D ⥤ C) := c.modelCategory sD
    (adjunction c sD sE u).IsQuillenAdjunction := by
  let (X : D ⥤ C) : u.HasRightKanExtension X := hasRightKanExtension c sD sE u X
  let : ModelCategory (E ⥤ C) := cE.modelCategory tE
  let : ModelCategory (D ⥤ C) := c.modelCategory sD
  exact KanExtensions.isQuillen_of_pointwise_left_classes u
    (c.fiveClasses sD).2.1 (cE.fiveClasses tE).2.1
    (c.fiveClasses sD).2.2.1 (cE.fiveClasses tE).2.2.1

end FromData

section ConventionalSource

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C] (u : D ⥤ E)

/-- Conventional source assumptions produce native right Kan existence for every F. -/
theorem hasRightKanExtension (F : D ⥤ C) : u.HasRightKanExtension F :=
  FromData.hasRightKanExtension (SourceConstruction.coefficientData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u F

/-- The public source entry preserves the entire native Ran functor and its original maps. -/
def ran : (D ⥤ C) ⥤ (E ⥤ C) :=
  FromData.ran (SourceConstruction.coefficientData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u

/-- The public source entry constructs the actual native restriction/Ran adjunction. -/
def adjunction : (whiskeringLeft D E C).obj u ⊣ ran u :=
  FromData.adjunction (SourceConstruction.coefficientData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u

/-- All public native object and map choices are unchanged. -/
theorem ran_eq_native :
    letI (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension u F
    ran (C := C) u = u.ran := rfl

/-- The same whole native unit/counit and adjunct function are returned publicly. -/
theorem adjunction_eq_native :
    letI (F : D ⥤ C) : u.HasRightKanExtension F := hasRightKanExtension u F
    adjunction (C := C) u = u.ranAdjunction C := rfl

/-- The source-constructed injective models make the actual public adjunction Quillen. -/
theorem isQuillen :
    letI : ModelCategory (E ⥤ C) := SourceConstruction.modelCategory (D := E) (C := C)
    letI : ModelCategory (D ⥤ C) := SourceConstruction.modelCategory (D := D) (C := C)
    (adjunction (C := C) u).IsQuillenAdjunction :=
  FromData.isQuillen (SourceConstruction.coefficientData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u
    (SourceConstruction.coefficientData C)
    (SourceConstruction.essentialIndex (D := E) (C := C))

end ConventionalSource

end HomotopicalAlgebra.FunctorInjective.SourceKanExtensions
