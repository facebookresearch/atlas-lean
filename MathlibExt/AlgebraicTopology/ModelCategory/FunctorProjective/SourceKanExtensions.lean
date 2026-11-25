/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.KanExtensions
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Native left Kan extensions on original source projective models

The actual coefficient generation supplies working-size colimits. The
original source and target index equivalences give the complete original
comma bounds. Native left Kan existence, the whole Lan functor and its
actual restriction adjunction are therefore constructed on the unchanged
original categories. Independent rank and working-universe choices may
construct the second projective model.

This is *Higher Topos Theory*, author version of April 9, 2017,
Proposition A.2.8.7(1), printed page 833 (PDF page 851), extended through
the actual essentially small original index equivalences.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uE vE uC vC

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace HomotopicalAlgebra.FunctorProjective.SourceKanExtensions

namespace FromData

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (sD : EssentialIndexData.{w} D C) (sE : EssentialIndexData.{w} E C) (u : D ⥤ E)

include d sD sE

/-- Genuine coefficient generation supplies every original left-comma colimit. -/
theorem hasCommaColimits (e : E) : HasColimitsOfShape (CostructuredArrow u e) C := by
  -- Use the supplied source and target equivalences, as in EssentialIndexBounds.
  let : LocallySmall.{w} E := sE.locallySmallIndex
  let : Small.{w} (CostructuredArrow (sD.equivalence.inverse ⋙ u) e) := inferInstance
  let : LocallySmall.{w} sD.index := locallySmall_self sD.index
  let : EssentiallySmall.{w} (CostructuredArrow u e) :=
    (essentiallySmall_congr (CostructuredArrow.pre sD.equivalence.inverse u e).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  exact d.hasColimitsOfShape

/-- Pointwise left Kan existence is derived on the original comma diagrams. -/
theorem hasPointwiseLeftKanExtension (F : D ⥤ C) : u.HasPointwiseLeftKanExtension F := by
  intro e
  let : HasColimitsOfShape (CostructuredArrow u e) C := hasCommaColimits d sD sE u e
  infer_instance

/-- The original coefficient/index sources construct native Lan existence for every F. -/
theorem hasLeftKanExtension (F : D ⥤ C) : u.HasLeftKanExtension F := by
  let : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
  infer_instance

/-- The complete original native Lan functor uses these constructed source witnesses. -/
def lan : (D ⥤ C) ⥤ (E ⥤ C) := by
  let (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension d sD sE u F
  exact u.lan

/-- Construct the actual native Lan/restriction adjunction on the original categories. -/
def adjunction : lan d sD sE u ⊣ (whiskeringLeft D E C).obj u := by
  let (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension d sD sE u F
  exact u.lanAdjunction C

/-- The returned whole object and map functor is the same original native Lan. -/
theorem lan_eq_native :
    letI (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension d sD sE u F
    lan d sD sE u = u.lan := rfl

/-- Both whole natural unit/counit transformations and all adjunct functions remain native. -/
theorem adjunction_eq_native :
    letI (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension d sD sE u F
    adjunction d sD sE u = u.lanAdjunction C := rfl

/-- Every original natural transformation retains its complete native Lan map. -/
theorem lan_map {F G : D ⥤ C} (α : F ⟶ G) :
    letI (X : D ⥤ C) : u.HasLeftKanExtension X := hasLeftKanExtension d sD sE u X
    (lan d sD sE u).map α = u.lan.map α := rfl

/-- The native value compares to the colimit of the ORIGINAL left comma diagram. -/
def evaluationIso (F : D ⥤ C) (e : E) :
    letI : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
    ((lan d sD sE u).obj F).obj e ≅ colimit (CostructuredArrow.proj u e ⋙ F) := by
  let (X : D ⥤ C) : u.HasLeftKanExtension X := hasLeftKanExtension d sD sE u X
  let : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
  exact u.leftKanExtensionObjIsoColimit F e

/-- The forward comparison retains the full original unit and comma-index action. -/
theorem evaluationIso_hom_injection (F : D ⥤ C) (e : E) (a : CostructuredArrow u e) :
    letI : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
    ((adjunction d sD sE u).unit.app F).app a.left ≫
        ((lan d sD sE u).obj F).map a.hom ≫ (evaluationIso d sD sE u F e).hom =
      colimit.ι (CostructuredArrow.proj u e ⋙ F) a := by
  let (X : D ⥤ C) : u.HasLeftKanExtension X := hasLeftKanExtension d sD sE u X
  let : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
  change ((u.lanAdjunction C).unit.app F).app a.left ≫
    (u.leftKanExtension F).map a.hom ≫ (u.leftKanExtensionObjIsoColimit F e).hom = _
  rw [Functor.lanAdjunction_unit]
  exact u.ι_leftKanExtensionObjIsoColimit_hom F e a

/-- The inverse comparison retains each original colimit injection and the same unit leg. -/
theorem evaluationIso_inv_injection (F : D ⥤ C) (e : E) (a : CostructuredArrow u e) :
    letI : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
    colimit.ι (CostructuredArrow.proj u e ⋙ F) a ≫ (evaluationIso d sD sE u F e).inv =
      ((adjunction d sD sE u).unit.app F).app a.left ≫
        ((lan d sD sE u).obj F).map a.hom := by
  let (X : D ⥤ C) : u.HasLeftKanExtension X := hasLeftKanExtension d sD sE u X
  let : u.HasPointwiseLeftKanExtension F := hasPointwiseLeftKanExtension d sD sE u F
  change colimit.ι _ a ≫ (u.leftKanExtensionObjIsoColimit F e).inv =
    ((u.lanAdjunction C).unit.app F).app a.left ≫ (u.leftKanExtension F).map a.hom
  rw [Functor.lanAdjunction_unit]
  exact u.ι_leftKanExtensionObjIsoColimit_inv F e a

/-- The actual unit remains natural on every original source transformation. -/
theorem unit_naturality {F G : D ⥤ C} (α : F ⟶ G) :
    α ≫ (adjunction d sD sE u).unit.app G =
      (adjunction d sD sE u).unit.app F ≫
        ((whiskeringLeft D E C).obj u).map ((lan d sD sE u).map α) :=
  (adjunction d sD sE u).unit.naturality α

/-- The whole actual counit retains every original target-index transformation. -/
theorem counit_naturality {F G : E ⥤ C} (α : F ⟶ G) :
    (lan d sD sE u).map (((whiskeringLeft D E C).obj u).map α) ≫
        (adjunction d sD sE u).counit.app G =
      (adjunction d sD sE u).counit.app F ≫ α :=
  (adjunction d sD sE u).counit.naturality α

/-- The native Lan-side triangle is a whole natural-transformation identity. -/
theorem left_triangle (F : D ⥤ C) :
    (lan d sD sE u).map ((adjunction d sD sE u).unit.app F) ≫
      (adjunction d sD sE u).counit.app ((lan d sD sE u).obj F) = 𝟙 _ :=
  (adjunction d sD sE u).left_triangle_components F

/-- The actual restriction-side triangle preserves the same whole unit/counit. -/
theorem right_triangle (F : E ⥤ C) :
    (adjunction d sD sE u).unit.app (((whiskeringLeft D E C).obj u).obj F) ≫
      ((whiskeringLeft D E C).obj u).map ((adjunction d sD sE u).counit.app F) = 𝟙 _ :=
  (adjunction d sD sE u).right_triangle_components F

variable {κ' : Cardinal.{w'}} [Fact κ'.IsRegular] [OrderBot κ'.ord.ToType]

/-- Independent actual source choices construct both models, and their proved
pointwise right classes make this same original native adjunction Quillen. -/
theorem isQuillen (dE : CofibrantGenerationData C κ') (tE : EssentialIndexData.{w'} E C) :
    letI : ModelCategory (D ⥤ C) := SourceConstruction.FromData.modelCategory d sD
    letI : ModelCategory (E ⥤ C) := SourceConstruction.FromData.modelCategory dE tE
    (adjunction d sD sE u).IsQuillenAdjunction := by
  let (X : D ⥤ C) : u.HasLeftKanExtension X := hasLeftKanExtension d sD sE u X
  let : ModelCategory (D ⥤ C) := SourceConstruction.FromData.modelCategory d sD
  let : ModelCategory (E ⥤ C) := SourceConstruction.FromData.modelCategory dE tE
  exact KanExtensions.isQuillen_of_pointwise_right_classes u
    (SourceConstruction.FromData.five_classes d sD).2.1
    (SourceConstruction.FromData.five_classes dE tE).2.1
    (SourceConstruction.FromData.five_classes d sD).2.2.1
    (SourceConstruction.FromData.five_classes dE tE).2.2.1

end FromData

section ConventionalSource

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C] (u : D ⥤ E)

local instance coefficientRegular : Fact (SourceConstruction.cardinal C).IsRegular :=
  SourceConstruction.cardinal_regular C
/-- The same original combinatorial source witness supplies its native ordinal bottom. -/
local instance coefficientBottom : OrderBot (SourceConstruction.cardinal C).ord.ToType :=
  SourceConstruction.orderBot C

/-- Conventional combinatorial/index sources produce native Lan existence for every F. -/
theorem hasLeftKanExtension (F : D ⥤ C) : u.HasLeftKanExtension F :=
  FromData.hasLeftKanExtension (SourceConstruction.baseData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u F

/-- The public source constructor retains the complete original native Lan functor. -/
def lan : (D ⥤ C) ⥤ (E ⥤ C) :=
  FromData.lan (SourceConstruction.baseData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u

/-- The original native adjunction is returned from those source witnesses. -/
def adjunction : lan u ⊣ (whiskeringLeft D E C).obj u :=
  FromData.adjunction (SourceConstruction.baseData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u

/-- All original object and map choices are exactly the existing native ones. -/
theorem lan_eq_native :
    letI (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension u F
    lan (C := C) u = u.lan := rfl

/-- The complete public unit/counit and all original adjunct functions remain native. -/
theorem adjunction_eq_native :
    letI (F : D ⥤ C) : u.HasLeftKanExtension F := hasLeftKanExtension u F
    adjunction (C := C) u = u.lanAdjunction C := rfl

/-- Both conventional source-constructed projective models make the native adjunction Quillen. -/
theorem isQuillen :
    letI : ModelCategory (D ⥤ C) := SourceConstruction.modelCategory (D := D) (C := C)
    letI : ModelCategory (E ⥤ C) := SourceConstruction.modelCategory (D := E) (C := C)
    (adjunction (C := C) u).IsQuillenAdjunction :=
  FromData.isQuillen (SourceConstruction.baseData C)
    (SourceConstruction.essentialIndex (D := D) (C := C))
    (SourceConstruction.essentialIndex (D := E) (C := C)) u
    (SourceConstruction.baseData C) (SourceConstruction.essentialIndex (D := E) (C := C))

end ConventionalSource

end HomotopicalAlgebra.FunctorProjective.SourceKanExtensions
