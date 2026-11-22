/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.ScalarLeibnizAssociator
public import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.LeibnizPullbackMaps

/-!
# Entire scalar cotensor and mapping-corner interchange

The actual Leibniz adjunctions are composed using the proved scalar associator
NatIso. Both entire Arrow maps, their units and counits, and arbitrary given
pullback choices are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u₁ u₂ u₃ v₁ v₂ v₃ u v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed



namespace PointedCGWH.EnrichedScalarCotensorInterchange

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- The category of enriched diagrams valued in pointed CGWH spaces. -/
abbrev Diagram := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev scalar : PointedCGWH.{u, v} ⥤ Diagram (I := I) ⥤ Diagram (I := I) :=
    ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)
/-- The scalar cotensor functor on pointed CGWH enriched diagrams. -/
abbrev cotensorScalar : PointedCGWH.{u, v}ᵒᵖ ⥤ Diagram (I := I) ⥤ Diagram (I := I) :=
    ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v}) (A := I)
/-- The enriched mapping-object bifunctor on pointed CGWH diagrams. -/
abbrev mapping : (Diagram (I := I))ᵒᵖ ⥤ Diagram (I := I) ⥤ PointedCGWH.{u, v} :=
    WeightedEndVariance.bifunctor (V := PointedCGWH.{u, v}) (I := I)

open PointedCGWH.EnrichedScalarLeibnizAssociator

/-- The complete native mapping-corner functor retains its original contravariant arrow. -/
abbrev mappingCorner {F G : Diagram (I := I)} (f : F ⟶ G) :
    Arrow (Diagram (I := I)) ⥤ Arrow PointedCGWH.{u, v} :=
  (mapping.{u, v} (I := I)).leibnizPullback.obj (op (Arrow.mk f))

/-- The complete native cotensor corner retains its original coefficient arrow. -/
abbrev cotensorCorner {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    Arrow (Diagram (I := I)) ⥤ Arrow (Diagram (I := I)) :=
  (cotensorScalar.{u, v} (I := I)).leibnizPullback.obj (op (Arrow.mk j))

/-- The complete native internal-Hom corner retains its original coefficient arrow. -/
abbrev internalHomCorner {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} :=
  MonoidalClosed.internalHom.leibnizPullback.obj (op (Arrow.mk j))

/-- The original scalar tensor-cotensor adjunction lifts to the entire Arrow category. -/
def scalarArrowAdjunction {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    scalarPushout (I := I) j ⊣ cotensorCorner (I := I) j :=
  ((scalar.{u, v} (I := I)).leibnizAdjunction (cotensorScalar.{u, v} (I := I))
    (ScalarLeibniz.parametrizedAdjunction (V := PointedCGWH.{u, v}) (A := I))).adj (Arrow.mk j)

/-- The original tensor-mapping adjunction lifts to the entire Arrow category. -/
def mappingArrowAdjunction {F G : Diagram (I := I)} (f : F ⟶ G) :
    mappingTensor f ⊣ mappingCorner f :=
  ((scalar.{u, v} (I := I)).flip.leibnizAdjunction (mapping.{u, v} (I := I))
    (PointedCGWH.NativeOriginalParametrizedMapping.adjunction (I := I))).adj (Arrow.mk f)

/-- The original ambient tensor/internal-Hom adjunction lifts to entire base arrows. -/
def baseArrowAdjunction {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    basePushout j ⊣ internalHomCorner j :=
  ((curriedTensor PointedCGWH.{u, v}).leibnizAdjunction MonoidalClosed.internalHom
    MonoidalClosed.internalHomAdjunction₂).adj (Arrow.mk j)

/-- The first genuine composite retains the native mapping and scalar units and counits. -/
def mappingThenScalarAdjunction {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    mappingTensor f ⋙ scalarPushout (I := I) j ⊣ cotensorCorner (I := I) j ⋙ mappingCorner f :=
  (mappingArrowAdjunction f).comp (scalarArrowAdjunction j)

/-- The second genuine composite retains the native base and mapping units and counits. -/
def baseThenMappingAdjunction {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    basePushout j ⋙ mappingTensor f ⊣ mappingCorner f ⋙ internalHomCorner j :=
  (baseArrowAdjunction j).comp (mappingArrowAdjunction f)

/-- Retarget the genuine second composite along the entire proved Arrow associator. -/
def transportedBaseMappingAdjunction {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    mappingTensor f ⋙ scalarPushout j ⊣ mappingCorner f ⋙ internalHomCorner j :=
  (baseThenMappingAdjunction j f).ofNatIsoLeft (associatorNatIso j f)

/-- Entire cotensor/mapping interchange follows from the actual three Leibniz adjunctions. -/
def cotensorMappingIso {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    cotensorCorner j ⋙ mappingCorner f ≅ mappingCorner f ⋙ internalHomCorner j :=
  Adjunction.rightAdjointUniq (mappingThenScalarAdjunction j f)
    (transportedBaseMappingAdjunction j f)

/-- The complete interchange forward map preserves the actual composite unit. -/
theorem cotensorMappingIso_unit {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    (mappingThenScalarAdjunction j f).unit ≫
      Functor.whiskerLeft (mappingTensor f ⋙ scalarPushout j) (cotensorMappingIso j f).hom =
        (transportedBaseMappingAdjunction j f).unit :=
  Adjunction.unit_rightAdjointUniq_hom (mappingThenScalarAdjunction j f)
    (transportedBaseMappingAdjunction j f)

/-- The complete interchange forward map preserves the actual composite counit. -/
theorem cotensorMappingIso_counit {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    Functor.whiskerRight (cotensorMappingIso j f).hom (mappingTensor f ⋙ scalarPushout j) ≫
      (transportedBaseMappingAdjunction j f).counit = (mappingThenScalarAdjunction j f).counit :=
  Adjunction.rightAdjointUniq_hom_counit (mappingThenScalarAdjunction j f)
    (transportedBaseMappingAdjunction j f)

/-- The inverse is the complete actual interchange with the two genuine adjunctions exchanged. -/
theorem cotensorMappingIso_inv {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G : Diagram (I := I)} (f : F ⟶ G) :
    (cotensorMappingIso j f).inv =
      (Adjunction.rightAdjointUniq (transportedBaseMappingAdjunction j f)
        (mappingThenScalarAdjunction j f)).hom := rfl

/-- Every original arrow and all four given pullback squares are retained by interchange. -/
def givenSquareInterchangeIso {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {F G X Y : Diagram (I := I)} (f : F ⟶ G) (p : X ⟶ Y)
    (cot : (cotensorScalar.{u, v} (I := I)).PullbackObjObj j p)
    (left : (mapping.{u, v} (I := I)).PullbackObjObj f cot.π)
    (inner : (mapping.{u, v} (I := I)).PullbackObjObj f p)
    (right : MonoidalClosed.internalHom.PullbackObjObj j inner.π) :
    Arrow.mk left.π ≅ Arrow.mk right.π :=
  let cotToChosen := Functor.PullbackObjObj.canonicalArrowIso (G := cotensorScalar.{u, v} (I := I))
      j p cot
  let leftToChosen := Functor.PullbackObjObj.canonicalArrowIso (G := mapping.{u, v} (I := I)) f
      cot.π left ≪≫
    (mappingCorner f).mapIso cotToChosen
  let innerToChosen := Functor.PullbackObjObj.canonicalArrowIso (G := mapping.{u, v} (I := I)) f p
      inner
  let rightToChosen := Functor.PullbackObjObj.canonicalArrowIso
      (G := MonoidalClosed.internalHom) j inner.π right ≪≫
    (internalHomCorner j).mapIso innerToChosen
  leftToChosen ≪≫ (cotensorMappingIso j f).app (Arrow.mk p) ≪≫ rightToChosen.symm

end PointedCGWH.EnrichedScalarCotensorInterchange
