/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalModel
import MathlibExt.AlgebraicTopology.ModelCategory.ExplicitModelIdentity

/-!
# Conditional original orthogonal model identity Quillen records

The original level model and conditional stable model are actual model
values on the unchanged full native spectrum category. Model record
carriers let both contexts coexist. Their comparison functors retain
every underlying spectrum and map, including full Hom functions, units,
counits, naturality and triangle equations.

The original cofibration equality and inclusion of original level weak
maps give the actual identity Quillen adjunction. The reverse fibration
and trivial-fibration laws follow from the actual model axioms. All
stable model views retain the exact pending original comparison premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalQuillen

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The unchanged original native level model is the actual source record. -/
abbrev levelModel : ModelCategory C.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B) (A := O)

/-- The level record context keeps every original underlying object and map. -/
abbrev LevelCarrier := ExplicitModelIdentity.Carrier (levelModel.{u, v} (B := B))

/-- The stable record context keeps the same actual native objects and maps. -/
abbrev StableCarrier (hComparison : ComparisonHomBijections.{u, v} (B := B)) :=
  ExplicitModelIdentity.Carrier (ConditionalModel.modelCategory hComparison)

/-- The full forward identity comparison retains the two actual model contexts. -/
def levelToStable (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    LevelCarrier.{u, v} (B := B) ⥤ StableCarrier hComparison :=
  ExplicitModelIdentity.comparison levelModel (ConditionalModel.modelCategory hComparison)

/-- The full reverse identity comparison retains the same original model values. -/
def stableToLevel (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    StableCarrier hComparison ⥤ LevelCarrier.{u, v} (B := B) :=
  ExplicitModelIdentity.comparison (ConditionalModel.modelCategory hComparison) levelModel

/-- The actual identity adjunction uses exactly these two full comparison functions. -/
def adjunction (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    levelToStable hComparison ⊣ stableToLevel hComparison :=
  ExplicitModelIdentity.identityAdjunction levelModel (ConditionalModel.modelCategory hComparison)

/-- Every full underlying object in both comparison directions remains the original spectrum. -/
theorem comparison_objects (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : LevelCarrier.{u, v} (B := B)) (Y : StableCarrier hComparison) :
    ((levelToStable hComparison).obj X).1 = X.1 ∧
      ((stableToLevel hComparison).obj Y).1 = Y.1 := ⟨rfl, rfl⟩

/-- Every forward comparison map is the whole original native map. -/
theorem levelToStable_map_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : LevelCarrier.{u, v} (B := B)} (f : X ⟶ Y) :
    ((levelToStable hComparison).map f).hom = f.hom := rfl

/-- Every reverse comparison map is the same entire original native map. -/
theorem stableToLevel_map_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : StableCarrier hComparison} (f : X ⟶ Y) :
    ((stableToLevel hComparison).map f).hom = f.hom := rfl

/-- Both whole comparison functors retain the original object and map
functions after forgetting their model record contexts. -/
theorem comparison_toBase (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    levelToStable hComparison ⋙ ExplicitModelIdentity.toBase
        (ConditionalModel.modelCategory hComparison) = ExplicitModelIdentity.toBase levelModel ∧
      stableToLevel hComparison ⋙ ExplicitModelIdentity.toBase levelModel =
        ExplicitModelIdentity.toBase (ConditionalModel.modelCategory hComparison) := ⟨rfl, rfl⟩

/-- Every entire unit component is the original underlying spectrum identity. -/
theorem unit_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : LevelCarrier.{u, v} (B := B)) :
    ((adjunction hComparison).unit.app X).hom = 𝟙 X.1 :=
  ExplicitModelIdentity.identityAdjunction_unit_hom levelModel
    (ConditionalModel.modelCategory hComparison) X

/-- Every entire counit component is the original underlying target identity. -/
theorem counit_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (Y : StableCarrier hComparison) :
    ((adjunction hComparison).counit.app Y).hom = 𝟙 Y.1 :=
  ExplicitModelIdentity.identityAdjunction_counit_hom levelModel
    (ConditionalModel.modelCategory hComparison) Y

/-- The full forward Hom function retains every original native map. -/
theorem homEquiv_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : LevelCarrier.{u, v} (B := B)) (Y : StableCarrier hComparison)
    (f : (levelToStable hComparison).obj X ⟶ Y) :
    ((adjunction hComparison).homEquiv X Y f).hom = f.hom :=
  ExplicitModelIdentity.identityAdjunction_homEquiv_hom levelModel
    (ConditionalModel.modelCategory hComparison) X Y f

/-- Its full inverse Hom function retains the same entire native map. -/
theorem homEquiv_symm_hom (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : LevelCarrier.{u, v} (B := B)) (Y : StableCarrier hComparison)
    (f : X ⟶ (stableToLevel hComparison).obj Y) :
    (((adjunction hComparison).homEquiv X Y).symm f).hom = f.hom :=
  ExplicitModelIdentity.identityAdjunction_homEquiv_symm_hom levelModel
    (ConditionalModel.modelCategory hComparison) X Y f

/-- Every actual level source map retains the whole original unit naturality square. -/
theorem unit_naturality (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : LevelCarrier.{u, v} (B := B)} (f : X ⟶ Y) :
    f ≫ (adjunction hComparison).unit.app Y = (adjunction hComparison).unit.app X ≫
      (stableToLevel hComparison).map ((levelToStable hComparison).map f) :=
  (adjunction hComparison).unit.naturality f

/-- Every actual stable target map retains the whole original counit naturality square. -/
theorem counit_naturality (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : StableCarrier hComparison} (f : X ⟶ Y) :
    (levelToStable hComparison).map ((stableToLevel hComparison).map f) ≫
        (adjunction hComparison).counit.app Y = (adjunction hComparison).counit.app X ≫ f :=
  (adjunction hComparison).counit.naturality f

/-- The same full original unit and counit obey the first triangle at every level object. -/
theorem first_triangle (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : LevelCarrier.{u, v} (B := B)) :
    (levelToStable hComparison).map ((adjunction hComparison).unit.app X) ≫
      (adjunction hComparison).counit.app ((levelToStable hComparison).obj X) = 𝟙 _ :=
  (adjunction hComparison).left_triangle_components X

/-- Both same original maps obey the second triangle at every stable object. -/
theorem second_triangle (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (Y : StableCarrier hComparison) :
    (adjunction hComparison).unit.app ((stableToLevel hComparison).obj Y) ≫
      (stableToLevel hComparison).map ((adjunction hComparison).counit.app Y) = 𝟙 _ :=
  (adjunction hComparison).right_triangle_components Y

/-- Original ordinary cofibrations and actual level weak maps give
the conditional identity Quillen adjunction on the same native maps. -/
theorem isQuillen (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (adjunction hComparison).IsQuillenAdjunction :=
  ExplicitModelIdentity.identityAdjunction_isQuillen levelModel
    (ConditionalModel.modelCategory hComparison)
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq (B := B) (A := O))
    levelWeak_le_stableWeakEquivalences

/-- The whole forward identity preserves the original full ordinary cofibration class. -/
theorem preservesCofibrations (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    PreservesCofibrations (levelToStable hComparison) :=
  (isQuillen hComparison).preservesCofibrations

/-- It preserves the entire original level trivial-cofibration class. -/
theorem preservesTrivialCofibrations (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    PreservesTrivialCofibrations (levelToStable hComparison) :=
  (isQuillen hComparison).preservesTrivialCofibrations

/-- The same actual adjunction proves reverse full fibration preservation. -/
theorem preservesReverseFibrations (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    PreservesFibrations (stableToLevel hComparison) := by
  let _ := isQuillen hComparison
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := adjunction hComparison)

/-- Its same original reverse identity preserves every full trivial fibration as well. -/
theorem preservesReverseTrivialFibrations
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    PreservesTrivialFibrations (stableToLevel hComparison) := by
  let _ := isQuillen hComparison
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := adjunction hComparison)

/-- The actual model records have identical whole trivial-fibration classes,
as forced by the unchanged full ordinary cofibration class. -/
theorem actual_trivialFibrations_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    levelModel.categoryWithFibrations.fibrations ⊓
        levelModel.categoryWithWeakEquivalences.weakEquivalences =
      (ConditionalModel.modelCategory hComparison).categoryWithFibrations.fibrations ⊓
        (ConditionalModel.modelCategory
          hComparison).categoryWithWeakEquivalences.weakEquivalences :=
  ExplicitModelIdentity.actual_trivialFibrations_eq levelModel
    (ConditionalModel.modelCategory hComparison)
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq (B := B) (A := O))

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalQuillen
