/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableCofiberTriangle
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoArrowSource

/-!
# Original ordinary-stable cofiber triangles on all Ho arrows

Every actual ordinary-Ho arrow is represented between the original Q and
R objects. Its original source cofiber triangle is transported through
both full comparison isomorphisms. The resulting first arrow is the
unchanged caller's Ho morphism. The inclusion and boundary retain the
original inverse target comparison and suspension of the full source
comparison. Every Ho arrow therefore extends in the constructed source
triangle family, without a distinguished-triangle certificate as input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits Pretriangulated HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableHoArrowTriangle

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "H" => toHomotopyCategory C
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- The actual cofiber is the original Q-cofiber of the full original Q/R representative. -/
def cofiber {X Y : HomotopyCategory C} (f : X ⟶ Y) : HomotopyCategory C :=
  OrdinaryStablePuppeGroups.cofiberHo g Z hZ (OriginalOrdinaryHoArrowSource.sourceArrow g f)

/-- The full original inverse target comparison is followed by the same original cofiber inclusion. -/
def inclusion {X Y : HomotopyCategory C} (f : X ⟶ Y) : Y ⟶ cofiber g Z hZ f :=
  (OriginalOrdinaryHoArrowSource.targetIso g Y).inv ≫
    OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ
      (OriginalOrdinaryHoArrowSource.sourceArrow g f)

/-- The original boundary is followed by the actual suspension of the entire source comparison. -/
def boundary {X Y : HomotopyCategory C} (f : X ⟶ Y) : cofiber g Z hZ f ⟶ (Σ).obj X :=
  OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ
    (OriginalOrdinaryHoArrowSource.sourceArrow g f) ≫
      (Σ).map (OriginalOrdinaryHoArrowSource.sourceIso g X).hom

/-- Every full caller Ho arrow gives a native triangle with those same original source maps. -/
def triangle {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    Triangle (HomotopyCategory C) := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  refine Triangle.mk f (inclusion g Z hZ f) ?_
  change cofiber g Z hZ f ⟶ (Σ).obj X
  exact boundary g Z hZ f

/-- Both complete original Q/R comparisons and the actual cofiber identity give a whole triangle Iso. -/
def sourceTriangleIso {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    OrdinaryStableCofiberTriangle.triangle g Z hZ
      (OriginalOrdinaryHoArrowSource.sourceArrow g f) ≅ triangle g Z hZ f := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  refine Triangle.isoMk _ _ (OriginalOrdinaryHoArrowSource.sourceIso g X)
    (OriginalOrdinaryHoArrowSource.targetIso g Y) (Iso.refl (cofiber g Z hZ f)) ?_ ?_ ?_
  · change (H).map (OriginalOrdinaryHoArrowSource.representative g f) ≫
      (OriginalOrdinaryHoArrowSource.targetIso g Y).hom =
        (OriginalOrdinaryHoArrowSource.sourceIso g X).hom ≫ f
    rw [OriginalOrdinaryHoArrowSource.representative_fac]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ
        (OriginalOrdinaryHoArrowSource.sourceArrow g f) ≫ 𝟙 _ =
      (OriginalOrdinaryHoArrowSource.targetIso g Y).hom ≫
        ((OriginalOrdinaryHoArrowSource.targetIso g Y).inv ≫
          OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ
            (OriginalOrdinaryHoArrowSource.sourceArrow g f))
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · change OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ
        (OriginalOrdinaryHoArrowSource.sourceArrow g f) ≫
          (Σ).map (OriginalOrdinaryHoArrowSource.sourceIso g X).hom =
      𝟙 (cofiber g Z hZ f) ≫ boundary g Z hZ f
    exact (Category.id_comp (boundary g Z hZ f)).symm

/-- Every actual full Ho arrow has its constructed triangle in the original source family. -/
theorem triangle_mem {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    triangle g Z hZ f ∈ OrdinaryStableCofiberTriangle.sourceTriangles g Z hZ :=
  ⟨OriginalOrdinaryHoArrowSource.sourceArrow g f, ⟨(sourceTriangleIso g Z hZ f).symm⟩⟩

/-- All Ho morphisms extend through the actual cofiber maps in the original source triangle family. -/
theorem all_arrows_extend {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    ∃ (E : HomotopyCategory C) (i : Y ⟶ E) (d : E ⟶ (shiftFunctor (HomotopyCategory C) 1).obj X),
      Triangle.mk f i d ∈ OrdinaryStableCofiberTriangle.sourceTriangles g Z hZ := by
  let := OrdinaryStableSourceShiftHom.hasShift g
  exact ⟨cofiber g Z hZ f, inclusion g Z hZ f, boundary g Z hZ f, triangle_mem g Z hZ f⟩

end HomotopicalAlgebra.OrdinaryStableHoArrowTriangle
