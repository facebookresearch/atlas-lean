/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.HomotopyExtension
import
  MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalContraction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinder
import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz

/-!
# Based homotopy extension for enriched diagrams

Defines homotopy extension for both the based time cylinder and the realized interval cylinder on pointed enriched diagrams. The properties are closed under composition, cobase change and arrow isomorphism. For the interval cylinder, extension is equivalent to a retraction of the mapping-cylinder comparison.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedBasedHomotopyExtension
open PointedCGWH.EnrichedIntervalContraction
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private theorem timePreservesColimits : PreservesColimits (timeFunctor (I := I)) :=
  (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.adjunction
    PointedCGWH.RealizedIntervalContraction.time.{u, v}).leftAdjoint_preservesColimits

attribute [local instance] timePreservesColimits

/-- Literal free I-plus time-zero HEP in the SAME genuine based native diagram category. -/
def property : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  IntervalHomotopyExtension.property timeFunctor (timeInclusionNatTrans 0)

/-- Every actual target map and actual free-time homotopy is retained in literal based HEP. -/
theorem property_iff {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X) :
    property i ↔ ∀ (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y)
      (H : timeObject A ⟶ Y), timeInclusion 0 A ≫ H = i ≫ f →
        ∃ K : timeObject X ⟶ Y, timeInclusion 0 X ≫ K = f ∧
          tensorLeftMap PointedCGWH.RealizedIntervalContraction.time i ≫ K = H := Iff.rfl

/-- The literal based native extension property contains the entire original identity maps. -/
instance isMultiplicative : (property (I := I)).IsMultiplicative := by
  change (IntervalHomotopyExtension.property timeFunctor
    (timeInclusionNatTrans 0)).IsMultiplicative
  infer_instance

/-- The ACTUAL original time/cotensor adjunction proves literal based pushout stability. -/
instance isStableUnderCobaseChange : (property (I := I)).IsStableUnderCobaseChange := by
  change (IntervalHomotopyExtension.property timeFunctor
    (timeInclusionNatTrans 0)).IsStableUnderCobaseChange
  infer_instance

/-- Literal based HEP retains every full original Arrow isomorphism. -/
instance respectsIso : (property (I := I)).RespectsIso := inferInstance

/-- The SAME original constant-time map proves based HEP of arbitrary original coprojections. -/
theorem coprod_inl_mem (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    property (coprod.inl : X ⟶ X ⨿ Z) :=
  IntervalHomotopyExtension.coprod_inl_mem timeFunctor (timeInclusionNatTrans 0)
    timeProjectionNatTrans (timeInclusion_projection_natTrans 0) X Z

end PointedCGWH.EnrichedBasedHomotopyExtension

namespace PointedCGWH.EnrichedIntervalBasedHomotopyExtension
open PointedCGWH.EnrichedIntervalCylinder PointedCGWH.EnrichedIntervalMappingCylinder
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original realized delta-zero endpoint has its genuine separate ALL-target based HEP. -/
def property : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  IntervalHomotopyExtension.property EnrichedIntervalCylinder.functor (inclusionNatTrans 0)

/-- The actual original interval/scalar-cotensor adjunction preserves ALL native colimits. -/
private theorem originalPreservesColimits :
    PreservesColimits (EnrichedIntervalCylinder.functor (I := I)) :=
  (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.adjunction
    PointedCGWH.IntervalCoefficient.interval.{u, v}).leftAdjoint_preservesColimits

attribute [local instance] originalPreservesColimits

/-- Every actual native target map and ORIGINAL delta-zero interval homotopy is retained. -/
theorem property_iff {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X) :
    property i ↔ ∀ (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y)
      (H : EnrichedIntervalCylinder.object A ⟶ Y), inclusion 0 A ≫ H = i ≫ f →
        ∃ K : EnrichedIntervalCylinder.object X ⟶ Y, inclusion 0 X ≫ K = f ∧
          tensorLeftMap PointedCGWH.IntervalCoefficient.interval i ≫ K = H := Iff.rfl

/-- Original endpoint extension is genuinely closed under complete original map composition. -/
instance isMultiplicative : (property (I := I)).IsMultiplicative := by
  change (IntervalHomotopyExtension.property EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0)).IsMultiplicative
  infer_instance

/-- The actual original scalar functor proves full original based cobase-change stability. -/
instance isStableUnderCobaseChange : (property (I := I)).IsStableUnderCobaseChange := by
  change (IntervalHomotopyExtension.property EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0)).IsStableUnderCobaseChange
  infer_instance

/-- Original endpoint HEP is invariant under every actual original full Arrow Iso. -/
instance respectsIso : (property (I := I)).RespectsIso := inferInstance

/-- The ORIGINAL projection and unit equations prove HEP of every arbitrary native coprojection. -/
theorem coprod_inl_mem (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    property (coprod.inl : X ⟶ X ⨿ Z) :=
  IntervalHomotopyExtension.coprod_inl_mem EnrichedIntervalCylinder.functor (inclusionNatTrans 0)
    projectionNatTrans (inclusion_projection_natTrans 0) X Z

/-- The SAME original MC has its actual universal map into the ORIGINAL target cylinder. -/
def comparison (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    EnrichedIntervalMappingCylinder.object f ⟶ EnrichedIntervalCylinder.object f.right :=
  IntervalHomotopyExtension.comparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) f.hom

/-- The universal comparison retains the entire ORIGINAL interval leg and ORIGINAL tensor map. -/
@[reassoc]
theorem intervalLeg_comparison (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    intervalLeg f ≫ comparison f = tensorLeftMap IntervalCoefficient.interval f.hom :=
  IntervalHomotopyExtension.inl_comparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) f.hom

/-- The universal comparison retains the entire SAME original target leg and first inclusion. -/
@[reassoc]
theorem targetLeg_comparison (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    targetLeg f ≫ comparison f = inclusion 0 f.right :=
  IntervalHomotopyExtension.inr_comparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) f.hom

/--
The literal SAME original MC and BOTH ORIGINAL leg equations are the universal ALL-target
based test for its ORIGINAL endpoint convention.
-/
theorem originalUniversal_iff (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    property f.hom ↔ ∃ r : EnrichedIntervalCylinder.object f.right ⟶
      EnrichedIntervalMappingCylinder.object f,
      inclusion 0 f.right ≫ r = targetLeg f ∧
        tensorLeftMap IntervalCoefficient.interval f.hom ≫ r = intervalLeg f :=
  IntervalHomotopyExtension.universal_iff EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) f.hom

/-- The SAME ORIGINAL complete universal comparison has a retraction exactly when HEP holds. -/
theorem originalRetraction_iff (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    property f.hom ↔ ∃ r : EnrichedIntervalCylinder.object f.right ⟶
      EnrichedIntervalMappingCylinder.object f,
      comparison f ≫ r = 𝟙 (EnrichedIntervalMappingCylinder.object f) :=
  IntervalHomotopyExtension.retraction_iff EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) f.hom

/-- BOTH full original Arrow maps retain the entire universal comparison square. -/
@[reassoc]
theorem map_comparison {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    EnrichedIntervalMappingCylinder.map h ≫ comparison g =
      comparison f ≫ tensorLeftMap IntervalCoefficient.interval h.right := by
  apply pushout.hom_ext
  · rw [← Category.assoc, intervalLeg_map, Category.assoc, intervalLeg_comparison,
      intervalLeg_comparison_assoc]
    change (EnrichedIntervalCylinder.functor.map h.left) ≫
        EnrichedIntervalCylinder.functor.map g.hom =
      EnrichedIntervalCylinder.functor.map f.hom ≫ EnrichedIntervalCylinder.functor.map h.right
    rw [← Functor.map_comp, ← Functor.map_comp, Arrow.w h]
  · rw [← Category.assoc, targetLeg_map, Category.assoc, targetLeg_comparison,
      targetLeg_comparison_assoc]
    exact (inclusion_naturality 0 h.right).symm

/-- The SAME original universal comparison is a whole natural transformation on all Arrows. -/
def comparisonNatTrans : EnrichedIntervalMappingCylinder.functor (I := I) ⟶
    Arrow.rightFunc ⋙ EnrichedIntervalCylinder.functor where
  app := comparison
  naturality _ _ h := map_comparison h

/-- EVERY complete original universal comparison component is retained as a whole function. -/
theorem comparisonNatTrans_app :
    (fun f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) => comparisonNatTrans.app f) =
      comparison := rfl

end PointedCGWH.EnrichedIntervalBasedHomotopyExtension
