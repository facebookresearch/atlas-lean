/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval
public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder

/-!
# The actual interval action on native enriched diagrams

The coefficient is the original native realized interval. Both inclusions
and contraction use its original endpoints and augmentation and the genuine
scalar action unit isomorphism. Their full diagram naturality, all component
maps and both whole functor retractions are proved without a model premise.
Model-category cylinder classes and mapping-cylinder pushouts are separate.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat

namespace PointedCGWH.EnrichedIntervalCylinder

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original native interval tensors the whole genuine diagram. -/
abbrev object (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  tensorLeftObject IntervalCoefficient.interval X

/-- The original interval tensor action is a genuine diagram endofunctor. -/
def functor : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  EnrichedFunctorCat.tensorLeft IntervalCoefficient.interval

/-- Each spectrum inclusion uses the actual unit inverse and original coefficient endpoint. -/
@[no_expose]
def inclusion (i : Fin 2) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : X ⟶ object X :=
  (scalarUnitIso X).inv ≫ scalarTensorMap (IntervalCoefficient.endpoint i) X

private theorem inclusion_eq_private (i : Fin 2)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion i X = (scalarUnitIso X).inv ≫
      scalarTensorMap (IntervalCoefficient.endpoint i) X := rfl

/-- The entire inclusion retains both original chosen factors. -/
theorem inclusion_eq (i : Fin 2) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion i X = (scalarUnitIso X).inv ≫
      scalarTensorMap (IntervalCoefficient.endpoint i) X := inclusion_eq_private i X

/-- The contraction uses the same original coefficient augmentation and unit map. -/
@[no_expose]
def projection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : object X ⟶ X :=
  scalarTensorMap IntervalCoefficient.augmentation X ≫ (scalarUnitIso X).hom

private theorem projection_eq_private (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    projection X = scalarTensorMap IntervalCoefficient.augmentation X ≫
      (scalarUnitIso X).hom := rfl

/-- The entire contraction retains both original chosen factors. -/
theorem projection_eq (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    projection X = scalarTensorMap IntervalCoefficient.augmentation X ≫
      (scalarUnitIso X).hom := projection_eq_private X

private theorem unit_inverse_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (scalarUnitIso X).inv ≫ tensorLeftMap (𝟙_ PointedCGWH.{u, v}) f =
      f ≫ (scalarUnitIso Y).inv := by
  apply (cancel_mono (scalarUnitIso Y).hom).1
  calc
    ((scalarUnitIso X).inv ≫ tensorLeftMap (𝟙_ PointedCGWH.{u, v}) f) ≫
        (scalarUnitIso Y).hom =
      (scalarUnitIso X).inv ≫
        (tensorLeftMap (𝟙_ PointedCGWH.{u, v}) f ≫ (scalarUnitIso Y).hom) :=
      Category.assoc _ _ _
    _ = (scalarUnitIso X).inv ≫ ((scalarUnitIso X).hom ≫ f) := by
      rw [scalarUnitIso_naturality]
    _ = f := (scalarUnitIso X).inv_hom_id_assoc f
    _ = (f ≫ (scalarUnitIso Y).inv) ≫ (scalarUnitIso Y).hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The whole inclusion is natural in every genuine enriched diagram morphism. -/
@[reassoc]
theorem inclusion_naturality (i : Fin 2)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    inclusion i X ≫ tensorLeftMap IntervalCoefficient.interval f =
      f ≫ inclusion i Y := by
  rw [inclusion_eq, inclusion_eq, Category.assoc,
    ← scalarTensorMap_diagram_naturality, ← Category.assoc,
    unit_inverse_naturality, Category.assoc]

/-- The whole contraction is natural in every genuine enriched diagram morphism. -/
@[reassoc]
theorem projection_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    tensorLeftMap IntervalCoefficient.interval f ≫ projection Y =
      projection X ≫ f := by
  rw [projection_eq, projection_eq, ← Category.assoc,
    scalarTensorMap_diagram_naturality, Category.assoc,
    scalarUnitIso_naturality, ← Category.assoc]

/-- Both original diagram endpoints are sections of the same genuine contraction. -/
@[reassoc]
theorem inclusion_projection (i : Fin 2)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : inclusion i X ≫ projection X = 𝟙 X := by
  rw [inclusion_eq, projection_eq, Category.assoc,
    ← Category.assoc (scalarTensorMap (IntervalCoefficient.endpoint i) X)
      (scalarTensorMap IntervalCoefficient.augmentation X) (scalarUnitIso X).hom,
    ← scalarTensorMap_comp, IntervalCoefficient.endpoint_augmentation, scalarTensorMap_id]
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- Every component of the inclusion is the original inverse unitor and coefficient endpoint. -/
theorem inclusion_component (i : Fin 2)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component (inclusion i X) a = (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
      IntervalCoefficient.endpoint i ▷ X.toEnrichedFunctor.obj a := by
  rw [inclusion_eq, component_comp, scalarUnitIso_inv_component, scalarTensorMap_component]
  rfl

/-- Every component of contraction is the original coefficient augmentation and unitor. -/
theorem projection_component (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component (projection X) a =
      IntervalCoefficient.augmentation ▷ X.toEnrichedFunctor.obj a ≫
        (λ_ (X.toEnrichedFunctor.obj a)).hom := by
  rw [projection_eq, component_comp, scalarTensorMap_component, scalarUnitIso_hom_component]
  rfl

/-- The first and second endpoints are full natural transformations on actual diagrams. -/
def inclusionNatTrans (i : Fin 2) :
    𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ functor where
  app X := inclusion i X
  naturality _ _ f := (inclusion_naturality i f).symm

/-- The original contraction is a full natural transformation on actual diagrams. -/
def projectionNatTrans : functor ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  app X := projection X
  naturality _ _ f := projection_naturality f

/-- Both original endpoints retract as whole natural transformations, at every object and map. -/
theorem inclusion_projection_natTrans (i : Fin 2) :
    inclusionNatTrans (I := I) i ≫ projectionNatTrans =
      𝟙 (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) := by
  apply NatTrans.ext
  funext X
  change inclusion i X ≫ projection X = 𝟙 X
  exact inclusion_projection i X

/-- The original interval maps form the canonical functorial precylinder. -/
def precylinder : HomotopicalAlgebra.Precylinder
    (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) where
  I := functor
  i₀ := inclusionNatTrans 0
  i₁ := inclusionNatTrans 1
  π := projectionNatTrans
  i₀_π := inclusion_projection_natTrans 0
  i₁_π := inclusion_projection_natTrans 1

/-- The pointwise boundary is the canonical precylinder boundary map. -/
abbrev boundaryMap (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [HasBinaryCoproduct X X] :
    X ⨿ X ⟶ object X := (precylinder.app X).i

end PointedCGWH.EnrichedIntervalCylinder
