/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyMappingCalculation

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wM u v

open CategoryTheory MonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedHomotopyMappingCalculationClients

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

open HomotopyMappingSpaceCategory GeneratedFunctorialReplacements GeneratedHomotopyMappingCalculation

def original_calculation : GeneratedRightMappingEnrichment.bifunctor d ≅
    CompatibleRightMappingComparison.mixedLocalization d := calculation a m d

theorem original_calculation_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y ≫
        (((original_calculation a m d).hom.app (.op X)).app Y) =
      (((original_calculation a m d).hom.app (.op X')).app Y) ≫
        ((CompatibleRightMappingComparison.mixedLocalization d).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((original_calculation a m d).hom.naturality f.op)

theorem original_calculation_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((GeneratedRightMappingEnrichment.bifunctor d).obj (.op X)).map f ≫
        (((original_calculation a m d).hom.app (.op X)).app Y') =
      (((original_calculation a m d).hom.app (.op X)).app Y) ≫
        ((CompatibleRightMappingComparison.mixedLocalization d).obj (.op X)).map f :=
  ((original_calculation a m d).hom.app (.op X)).naturality f

theorem original_calculation_inverse_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((CompatibleRightMappingComparison.mixedLocalization d).map f.op).app Y ≫
        (((original_calculation a m d).inv.app (.op X)).app Y) =
      (((original_calculation a m d).inv.app (.op X')).app Y) ≫
        ((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((original_calculation a m d).inv.naturality f.op)

theorem original_calculation_inverse_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((CompatibleRightMappingComparison.mixedLocalization d).obj (.op X)).map f ≫
        (((original_calculation a m d).inv.app (.op X)).app Y') =
      (((original_calculation a m d).inv.app (.op X)).app Y) ≫
        ((GeneratedRightMappingEnrichment.bifunctor d).obj (.op X)).map f :=
  ((original_calculation a m d).inv.app (.op X)).naturality f

@[instance_reducible]
def original_mixed_enrichment : EnrichedCategory SpaceHo.{v} C := mixedEnrichment a m d

theorem original_mixed_objects (X Y : C) :
    (original_mixed_enrichment a m d).Hom X Y =
      localize.obj (SimplicialCategory.sHom ((Q d).obj X) ((R d).obj Y)) :=
  mixedEnrichment_hom a m d X Y

theorem original_mixed_unit (X : C) : mixedUnit a m d X =
    Functor.LaxMonoidal.ε localize ≫
      localize.map (eHomEquiv SSet ((counit d).app X ≫ (unit d).app X)) :=
  mixedUnit_calculation a m d X

theorem original_composition_comparison (X Y Z : C) :
    ((((original_calculation a m d).hom.app (.op X)).app Y) ⊗ₘ
        (((original_calculation a m d).hom.app (.op Y)).app Z)) ≫ mixedComp a m d X Y Z =
      GeneratedRightMappingEnrichment.comp d X Y Z ≫
        (((original_calculation a m d).hom.app (.op X)).app Z) := calculation_comp a m d X Y Z

theorem original_mixed_left_unit (X Y : C) :
    (λ_ (localize.obj (GeneratedDerivedMapping.space d X Y))).inv ≫
        mixedUnit a m d X ▷ _ ≫ mixedComp a m d X X Y =
      𝟙 (localize.obj (GeneratedDerivedMapping.space d X Y)) := mixedComp_leftUnit a m d X Y

theorem original_mixed_right_unit (X Y : C) :
    (ρ_ (localize.obj (GeneratedDerivedMapping.space d X Y))).inv ≫
        _ ◁ mixedUnit a m d Y ≫ mixedComp a m d X Y Y =
      𝟙 (localize.obj (GeneratedDerivedMapping.space d X Y)) := mixedComp_rightUnit a m d X Y

theorem original_mixed_associativity (W X Y Z : C) :
    (α_ (localize.obj (GeneratedDerivedMapping.space d W X))
        (localize.obj (GeneratedDerivedMapping.space d X Y))
        (localize.obj (GeneratedDerivedMapping.space d Y Z))).inv ≫
        mixedComp a m d W X Y ▷ _ ≫ mixedComp a m d W Y Z =
      _ ◁ mixedComp a m d X Y Z ≫ mixedComp a m d W X Z := mixedComp_assoc a m d W X Y Z

def original_endpoint (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    localize.obj (SimplicialCategory.sHom X Y) ≅ GeneratedRightMappingEnrichment.space d X Y :=
  ordinaryCalculation a m d X Y

theorem original_endpoint_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) [IsFibrant Y] :
    localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Y) ≫
        (original_endpoint a m d X Y).hom =
      (original_endpoint a m d X' Y).hom ≫ GeneratedRightMappingEnrichment.precomp d f Y :=
  ordinaryCalculation_source a m d f Y

theorem original_endpoint_target (X : C) [IsCofibrant X]
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    localize.map (((SimplicialCategory.sHomFunctor C).obj (.op X)).map f) ≫
        (original_endpoint a m d X Y').hom =
      (original_endpoint a m d X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp d X f :=
  ordinaryCalculation_target a m d X f

theorem original_endpoint_inverse_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.precomp d f Y ≫ (original_endpoint a m d X Y).inv =
      (original_endpoint a m d X' Y).inv ≫
        localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Y) :=
  ordinaryCalculation_inverse_source a m d f Y

theorem original_endpoint_inverse_target (X : C) [IsCofibrant X]
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    GeneratedRightMappingEnrichment.postcomp d X f ≫ (original_endpoint a m d X Y').inv =
      (original_endpoint a m d X Y).inv ≫
        localize.map (((SimplicialCategory.sHomFunctor C).obj (.op X)).map f) :=
  ordinaryCalculation_inverse_target a m d X f

theorem original_endpoint_point {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    localize.map (eHomEquiv SSet f) ≫ (original_endpoint a m d X Y).hom =
      localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) :=
  ordinaryCalculation_point a m d f

theorem original_endpoint_inverse_point {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) ≫ (original_endpoint a m d X Y).inv =
      localize.map (eHomEquiv SSet f) := ordinaryCalculation_inverse_point a m d f

theorem original_endpoint_unit (X : C) [IsCofibrant X] [IsFibrant X] :
    (Functor.LaxMonoidal.ε localize ≫ localize.map (eId SSet X)) ≫
        (original_endpoint a m d X X).hom = GeneratedRightMappingEnrichment.unit d X :=
  ordinaryCalculation_unit a m d X

def original_strict_bifunctor : strictHoBifunctor d ≅ GeneratedRightMappingEnrichment.bifunctor d :=
  strictBifunctorCalculation a m d

theorem original_strict_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((strictHoBifunctor d).map f.op).app Y ≫ (((original_strict_bifunctor a m d).hom.app (.op X)).app Y) =
      (((original_strict_bifunctor a m d).hom.app (.op X')).app Y) ≫
        ((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((original_strict_bifunctor a m d).hom.naturality f.op)

theorem original_strict_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((strictHoBifunctor d).obj (.op X)).map f ≫ (((original_strict_bifunctor a m d).hom.app (.op X)).app Y') =
      (((original_strict_bifunctor a m d).hom.app (.op X)).app Y) ≫
        ((GeneratedRightMappingEnrichment.bifunctor d).obj (.op X)).map f :=
  ((original_strict_bifunctor a m d).hom.app (.op X)).naturality f

theorem original_strict_unit (X : C) :
    (Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.strictUnit d X)) ≫
        (strictCalculation a m d X X).hom = GeneratedRightMappingEnrichment.unit d X :=
  strictCalculation_unit a m d X

def original_single_factory_calculation : GeneratedRightMappingEnrichment.bifunctor d ≅
    CompatibleRightMappingComparison.mixedLocalization d := originalCalculation a d

@[instance_reducible]
def original_single_factory_enrichment : EnrichedCategory SpaceHo.{v} C := originalMixedEnrichment a d

def original_single_factory_endpoint (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    localize.obj (SimplicialCategory.sHom X Y) ≅ GeneratedRightMappingEnrichment.space d X Y :=
  originalEndpointCalculation a d X Y

end HomotopicalAlgebra.GeneratedHomotopyMappingCalculationClients
