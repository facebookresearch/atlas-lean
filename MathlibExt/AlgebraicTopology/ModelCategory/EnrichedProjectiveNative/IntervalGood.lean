/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalBoundaryModel

/-!
# Goodness of the same actual native diagram cylinder

The actual coefficient Quillen functor sends the original joint endpoint
cofibration to a native projective cofibration. Its genuine preserved
coproduct and original scalar unit maps identify that whole arrow with the
two original diagram inclusions. No goodness or source-model dictionary is
assumed. The original native diagram cylinder is retained unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uC vC uD vD u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedFunctorMapping
open PointedCGWH.EnrichedIntervalCylinder
open scoped CGWH.modelCategory



namespace PointedCGWH.EnrichedIntervalCylinderModel

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

omit B in
private instance scalarPreservesPair (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesColimitsOfShape (Discrete WalkingPair)
      (WeightedEndVariance.tensorBifunctor.flip.obj X) := by
  let _ : PreservesColimits (WeightedEndVariance.tensorBifunctor.flip.obj X) :=
    (tensorMappingAdjunction X).leftAdjoint_preservesColimits
  infer_instance

/-- The same actual native joint diagram inclusion. -/
abbrev jointMap (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    X ⨿ X ⟶ EnrichedIntervalCylinder.object X := EnrichedIntervalCylinder.boundaryMap X

omit B in
set_option backward.isDefEq.respectTransparency false in
/-- The whole native joint arrow is the original coefficient joint arrow under actual tensoring. -/
def jointMapArrowIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    Arrow.mk (jointMap X) ≅
      Arrow.mk ((WeightedEndVariance.tensorBifunctor.flip.obj X).map
        IntervalCoefficient.jointEndpoints) := by
  let e : (WeightedEndVariance.tensorBifunctor.flip.obj X).obj
      (𝟙_ PointedCGWH.{u, v}) ≅ X := scalarUnitIso X
  let F := WeightedEndVariance.tensorBifunctor.flip.obj X
  let _ : PreservesColimitsOfShape (Discrete WalkingPair) F := by
    exact scalarPreservesPair X
  let c : F.obj ((𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})) ≅ X ⨿ X :=
    (asIso (coprodComparison F (𝟙_ PointedCGWH.{u, v})
      (𝟙_ PointedCGWH.{u, v}))).symm ≪≫ coprod.mapIso e e
  refine Arrow.isoMk' _ _ c.symm (Iso.refl _) ?_
  rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  apply coprod.hom_ext
  · dsimp only [c, Iso.trans_inv, Iso.symm_inv, asIso_hom, coprod.mapIso]
    rw [← Category.assoc, coprod.inl_map_assoc, Category.assoc,
      inl_coprodComparison, ← CategoryTheory.Functor.map_comp, coprod.inl_desc]
    exact (inclusion_eq 0 X).symm.trans (coprod.inl_desc _ _).symm
  · dsimp only [c, Iso.trans_inv, Iso.symm_inv, asIso_hom, coprod.mapIso]
    rw [← Category.assoc, coprod.inr_map_assoc, Category.assoc,
      inr_coprodComparison, ← CategoryTheory.Functor.map_comp, coprod.inr_desc]
    exact (inclusion_eq 1 X).symm.trans (coprod.inr_desc _ _).symm

/-- The entire original joint map is projectively cofibrant for a cofibrant native source. -/
theorem jointMap_cofibration
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] : Cofibration (jointMap X) := by
  have hOriginal : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((WeightedEndVariance.tensorBifunctor.flip.obj X).map
        IntervalCoefficient.jointEndpoints) :=
    (coefficient_isQuillen X).preservesCofibrations _
      ((HomotopicalAlgebra.cofibration_iff _).mp IntervalCoefficient.jointEndpoints_cofibration)
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (((cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).arrow_mk_iso_iff
      (jointMapArrowIso X)).mpr hOriginal)

/-- The same literal native diagram cylinder is good; no supplied cylinder is selected. -/
theorem cylinder_isGood
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] : (cylinder X).IsGood where
  cofibration_i := jointMap_cofibration X

end PointedCGWH.EnrichedIntervalCylinderModel
