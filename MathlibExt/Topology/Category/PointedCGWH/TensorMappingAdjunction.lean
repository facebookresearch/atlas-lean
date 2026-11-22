/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.EnrichedScalarClosed
public import Mathlib.CategoryTheory.Adjunction.Basic
public import MathlibExt.CategoryTheory.Enriched.MappingParametrized

/-!
# Actual native tensor and mapping adjunction

For a fixed genuine native enriched diagram, scalar tensoring is left
adjoint to the full original mapping end. Both functors retain their
original scalar and diagram maps. Native small limits and the proved
positive graded correspondence supply the construction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory EnrichedFunctorCat MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.EnrichedFunctorMapping

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

set_option backward.isDefEq.respectTransparency false in
/-- The full native closed correspondence is natural in every genuine target arrow. -/
theorem tensorHomEquiv_target_naturality
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) (g : Y ⟶ Z) :
    tensorHomEquiv X Z T (f ≫ WeightedEndVariance.post X g) = tensorHomEquiv X Y T f ≫ g := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  rw [tensorHomEquiv_component, EnrichedFunctorCat.component_comp,
    tensorHomEquiv_component, Category.assoc, WeightedEndVariance.post_projection, ← Category.assoc,
    MonoidalClosed.uncurry_natural_right, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private def tensorMappingCore (F : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    Adjunction.CoreHomEquiv (WeightedEndVariance.tensorBifunctor.flip.obj F)
      (WeightedEndVariance.rightFunctor F) where
  homEquiv T Y := (tensorHomEquiv F Y T).symm
  homEquiv_naturality_left_symm h f := tensorHomEquiv_coefficient_naturality F _ h f
  homEquiv_naturality_right {X} {Y} {Y'} f g := by
    change EnrichedFunctorCat.tensorLeftObject X F ⟶ Y at f
    change (tensorHomEquiv F Y' X).symm (f ≫ g) =
      (tensorHomEquiv F Y X).symm f ≫ WeightedEndVariance.post F g
    apply (tensorHomEquiv F Y' X).injective
    calc
      _ = f ≫ g := (tensorHomEquiv F Y' X).apply_symm_apply (f ≫ g)
      _ = tensorHomEquiv F Y X ((tensorHomEquiv F Y X).symm f) ≫ g :=
        congrArg (fun t => t ≫ g) ((tensorHomEquiv F Y X).apply_symm_apply f).symm
      _ = _ := (tensorHomEquiv_target_naturality F X
        ((tensorHomEquiv F Y X).symm f) g).symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual native scalar tensoring is left adjoint to the original full mapping end. -/
@[no_expose]
def tensorMappingAdjunction (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeightedEndVariance.tensorBifunctor.flip.obj X ⊣ WeightedEndVariance.rightFunctor X :=
  Adjunction.mkOfHomEquiv (tensorMappingCore X)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorMappingAdjunction_homEquiv_private
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (T : PointedCGWH.{u, v}) :
    (tensorMappingAdjunction X).homEquiv T Y = (tensorHomEquiv X Y T).symm := by
  change (Adjunction.mkOfHomEquiv (tensorMappingCore X)).homEquiv T Y = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual adjunction retains the original native scalar-to-end correspondence. -/
theorem tensorMappingAdjunction_homEquiv
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (T : PointedCGWH.{u, v}) :
    (tensorMappingAdjunction X).homEquiv T Y = (tensorHomEquiv X Y T).symm :=
  tensorMappingAdjunction_homEquiv_private X Y T

set_option backward.isDefEq.respectTransparency false in
/-- Every actual unit projection is the inverse positive braid under currying. -/
theorem tensorMappingAdjunction_unit_π
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (T : PointedCGWH.{u, v}) (a : I) :
    (tensorMappingAdjunction X).unit.app T ≫ π X (EnrichedFunctorCat.tensorLeftObject T X) a =
      MonoidalClosed.curry ((β_ T (X.toEnrichedFunctor.obj a)).inv) := by
  rw [← (tensorMappingAdjunction X).homEquiv_id T, tensorMappingAdjunction_homEquiv]
  change (tensorHomEquiv X (EnrichedFunctorCat.tensorLeftObject T X) T).symm (𝟙 _) ≫
    π X (EnrichedFunctorCat.tensorLeftObject T X) a = _
  rw [tensorHomEquiv_symm_π, EnrichedFunctorCat.component_id]
  change MonoidalClosed.curry ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫
    𝟙 (T ⊗ X.toEnrichedFunctor.obj a)) = _
  rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual counit component is the positive braid followed by original end evaluation. -/
theorem tensorMappingAdjunction_counit_component
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    EnrichedFunctorCat.component ((tensorMappingAdjunction X).counit.app Y) a =
      (β_ (mappingObject X Y) (X.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (π X Y a) := by
  rw [← (tensorMappingAdjunction X).homEquiv_symm_id Y, tensorMappingAdjunction_homEquiv]
  change EnrichedFunctorCat.component (tensorHomEquiv X Y (mappingObject X Y) (𝟙 _)) a = _
  rw [tensorHomEquiv_component, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor and evaluation maps satisfy the complete left triangle identity. -/
theorem tensorMappingAdjunction_left_triangle
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (T : PointedCGWH.{u, v}) :
    EnrichedFunctorCat.scalarTensorMap ((tensorMappingAdjunction X).unit.app T) X ≫
        (tensorMappingAdjunction X).counit.app (EnrichedFunctorCat.tensorLeftObject T X) =
      𝟙 (EnrichedFunctorCat.tensorLeftObject T X) :=
  (tensorMappingAdjunction X).left_triangle_components T

set_option backward.isDefEq.respectTransparency false in
/-- The original end and evaluation maps satisfy the complete right triangle identity. -/
theorem tensorMappingAdjunction_right_triangle
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (tensorMappingAdjunction X).unit.app (mappingObject X Y) ≫
        WeightedEndVariance.post X ((tensorMappingAdjunction X).counit.app Y) =
      𝟙 (mappingObject X Y) := by
  have h := (tensorMappingAdjunction X).right_triangle_components Y
  change (tensorMappingAdjunction X).unit.app (mappingObject X Y) ≫
    WeightedEndVariance.post X ((tensorMappingAdjunction X).counit.app Y) =
      𝟙 (mappingObject X Y) at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit is natural in every native scalar morphism. -/
theorem tensorMappingAdjunction_unit_naturality
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {T T' : PointedCGWH.{u, v}} (h : T ⟶ T') :
    h ≫ (tensorMappingAdjunction X).unit.app T' =
      (tensorMappingAdjunction X).unit.app T ≫
        (WeightedEndVariance.tensorBifunctor.flip.obj X ⋙
          WeightedEndVariance.rightFunctor X).map h :=
  (tensorMappingAdjunction X).unit.naturality h

set_option backward.isDefEq.respectTransparency false in
/-- The actual counit is natural in every genuine native target transformation. -/
theorem tensorMappingAdjunction_counit_naturality
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I} (g : Y ⟶ Z) :
    EnrichedFunctorCat.scalarTensorMap (WeightedEndVariance.post X g) X ≫
        (tensorMappingAdjunction X).counit.app Z =
      (tensorMappingAdjunction X).counit.app Y ≫ g :=
  (tensorMappingAdjunction X).counit.naturality g

end PointedCGWH.EnrichedFunctorMapping
