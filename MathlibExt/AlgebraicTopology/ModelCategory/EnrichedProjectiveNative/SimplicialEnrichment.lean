/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSimplicialEnrichment
public import MathlibExt.Topology.Category.PointedCGWH.EnrichedFunctorCategory
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourceFunctor
public import MathlibExt.CategoryTheory.Enriched.Ordinary.MapHomWhisker

/-!
# The singular simplicial enrichment on genuine native enriched diagrams

The original weighted-end Hom objects, positive graded identity and
composition determine the native pointed enrichment. Applying the proved
native singular lax functor gives a simplicial enrichment on the same
ordinary enriched functor category.

The unit-Hom function, both original enriched field maps, and both
ordinary variance functions are explicit. The entire simplicial mapping
bifunctor is naturally isomorphic to singularization of the original
native mapping bifunctor, with identity components throughout.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open PointedCGWH.SingularHomotopyGeometry
open scoped Simplicial MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.SimplicialEnrichment

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] PointedCGWH.NativeSimplicial.singularLaxMonoidal
  PointedCGWH.EnrichedFunctorMapping.enrichedOrdinaryCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

/-- Original mapping-end projections construct the enriched evaluation at every actual index. -/
def enrichedEvaluation (a : I) :
    EnrichedFunctor PointedCGWH.{u, v}
      (EnrichedFunctorCat PointedCGWH.{u, v} I) PointedCGWH.{u, v} where
  obj X := X.toEnrichedFunctor.obj a
  map X Y := PointedCGWH.EnrichedFunctorMapping.π X Y a
  map_id X := PointedCGWH.EnrichedFunctorMapping.mappingIdentity_π X a
  map_comp X Y Z := PointedCGWH.EnrichedFunctorMapping.mappingComposition_π X Y Z a

/-- The complete enriched evaluation map is the original unit-graded component function. -/
theorem enrichedEvaluation_toOrdinary_map (a : I)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (enrichedEvaluation a).toOrdinaryFunctor.map f = EnrichedFunctorCat.component f a := by
  apply (eHomEquiv PointedCGWH.{u, v}).injective
  rw [EnrichedFunctor.toOrdinaryFunctor_map]
  change PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv X Y f ≫
    PointedCGWH.EnrichedFunctorMapping.π X Y a =
      eHomEquiv PointedCGWH.{u, v} (EnrichedFunctorCat.component f a)
  rw [PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv_π]
  exact (Equiv.apply_symm_apply (eHomEquiv PointedCGWH.{u, v}) (f.app a)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original enriched source whiskering is exactly the original full mapping-end weight map. -/
theorem nativeWhiskerRight
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    eHomWhiskerRight PointedCGWH.{u, v} f Z =
      Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
        X.toEnrichedFunctor f := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Z.toEnrichedFunctor
  intro a
  have h := EnrichedFunctor.map_eHomWhiskerRight (enrichedEvaluation a) f Z
  change eHomWhiskerRight PointedCGWH.{u, v} f Z ≫
      PointedCGWH.EnrichedFunctorMapping.π X Z a =
    PointedCGWH.EnrichedFunctorMapping.π Y Z a ≫
      eHomWhiskerRight PointedCGWH.{u, v}
        ((enrichedEvaluation a).toOrdinaryFunctor.map f) (Z.toEnrichedFunctor.obj a) at h
  rw [enrichedEvaluation_toOrdinary_map,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h.trans (Enriched.weightedEnd.mapWeight_π Y.toEnrichedFunctor
    Z.toEnrichedFunctor X.toEnrichedFunctor f a).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original enriched target whiskering is exactly the original full mapping-end target map. -/
theorem nativeWhiskerLeft (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Y Y' : EnrichedFunctorCat PointedCGWH.{u, v} I} (g : Y ⟶ Y') :
    eHomWhiskerLeft PointedCGWH.{u, v} X g =
      EnrichedFunctorCat.WeightedEndVariance.post X g := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y'.toEnrichedFunctor
  intro a
  let H := PointedCGWH.EnrichedFunctorMapping.mappingObject X Y
  let p := PointedCGWH.EnrichedFunctorMapping.π X Y a
  let q := g.app a
  have hTensor :
      (H ◁ PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv Y Y' g) ≫
        (p ⊗ₘ PointedCGWH.EnrichedFunctorMapping.π Y Y' a) = p ⊗ₘ q := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv_π]
  calc
    _ = (ρ_ H).inv ≫
        (H ◁ PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv Y Y' g) ≫
        (p ⊗ₘ PointedCGWH.EnrichedFunctorMapping.π Y Y' a) ≫
        eComp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
          (Y.toEnrichedFunctor.obj a) (Y'.toEnrichedFunctor.obj a) := by
      change (ρ_ H).inv ≫
        (H ◁ PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv Y Y' g) ≫
        PointedCGWH.EnrichedFunctorMapping.mappingComposition X Y Y' ≫
        PointedCGWH.EnrichedFunctorMapping.π X Y' a = _
      rw [PointedCGWH.EnrichedFunctorMapping.mappingComposition_π]
    _ = (ρ_ H).inv ≫ (p ⊗ₘ q) ≫
        eComp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
          (Y.toEnrichedFunctor.obj a) (Y'.toEnrichedFunctor.obj a) := by
      rw [reassoc_of% hTensor]
    _ = p ≫
        eHomWhiskerLeft PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
          (EnrichedFunctorCat.component g a) := by
      rw [rightUnitor_inv_comp_tensorHom_assoc]
      simp only [eHomWhiskerLeft, EnrichedFunctorCat.component, Equiv.apply_symm_apply]
      rfl
    _ = _ := by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
      exact (EnrichedFunctorCat.WeightedEndVariance.post_projection X g a).symm

/-- The original native weighted-end enrichment is singularized on the identical diagram carrier. -/
@[instance_reducible]
def simplicialCategory : SimplicialCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  PointedCGWH.NativeSimplicial.enrichedOrdinaryCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)

attribute [local instance] simplicialCategory

/-- The simplicial Hom is the singular complex of the original full native mapping end. -/
theorem sHom_eq (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SimplicialCategory.sHom X Y =
      singularFunctor.obj (PointedCGWH.EnrichedFunctorMapping.mappingObject X Y) := rfl

/-- The entire ordinary unit-Hom function keeps the original native mapping-Hom function. -/
theorem homEquiv_apply {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    eHomEquiv SSet.{v} f = Functor.LaxMonoidal.ε singularFunctor ≫
      singularFunctor.map (PointedCGWH.EnrichedFunctorMapping.mappingHomEquiv X Y f) :=
  PointedCGWH.NativeSimplicial.unitHomEquiv_apply _ _

/-- Simplicial identity is the singular lax unit followed by the unchanged native identity. -/
theorem identity (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    eId SSet.{v} X = Functor.LaxMonoidal.ε singularFunctor ≫
      singularFunctor.map (PointedCGWH.EnrichedFunctorMapping.mappingIdentity X) := rfl

/-- The complete simplicial composition singularizes the original positive graded composition. -/
theorem composition (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    eComp SSet.{v} X Y Z =
      Functor.LaxMonoidal.μ singularFunctor
          (PointedCGWH.EnrichedFunctorMapping.mappingObject X Y)
          (PointedCGWH.EnrichedFunctorMapping.mappingObject Y Z) ≫
        singularFunctor.map (PointedCGWH.EnrichedFunctorMapping.mappingComposition X Y Z) := rfl

/-- Every complete source-variance map is the singular image of the original enriched whisker. -/
theorem whiskerRight {X X' : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ X')
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    eHomWhiskerRight SSet.{v} f Y =
      singularFunctor.map (eHomWhiskerRight PointedCGWH.{u, v} f Y) :=
  PointedCGWH.NativeSimplicial.whiskerRight (EnrichedFunctorCat PointedCGWH.{u, v} I) f Y

/-- Every complete target-variance map is the singular image of the original enriched whisker. -/
theorem whiskerLeft (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Y Y' : EnrichedFunctorCat PointedCGWH.{u, v} I} (g : Y ⟶ Y') :
    eHomWhiskerLeft SSet.{v} X g =
      singularFunctor.map (eHomWhiskerLeft PointedCGWH.{u, v} X g) :=
  PointedCGWH.NativeSimplicial.whiskerLeft (EnrichedFunctorCat PointedCGWH.{u, v} I) X g

/-- Every whole simplicial source map is singularization of the literal original weight map. -/
theorem source_map
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f.op).app Z =
      singularFunctor.map (Enriched.weightedEnd.mapWeight
        Y.toEnrichedFunctor Z.toEnrichedFunctor X.toEnrichedFunctor f) :=
  (whiskerRight f Z).trans (congrArg singularFunctor.map (nativeWhiskerRight f Z))

/-- Every whole simplicial target map is singularization of the literal original target map. -/
theorem target_map (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Y Y' : EnrichedFunctorCat PointedCGWH.{u, v} I} (g : Y ⟶ Y') :
    ((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      (Opposite.op X)).map g =
      singularFunctor.map (EnrichedFunctorCat.WeightedEndVariance.post X g) :=
  (whiskerLeft X g).trans (congrArg singularFunctor.map (nativeWhiskerLeft X g))

/-- Singularization of the entire original native enriched Hom bifunctor. -/
def singularMappingFunctor : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ SSet.{v} :=
  EnrichedFunctorCat.WeightedEndVariance.bifunctor ⋙
    (Functor.whiskeringRight (EnrichedFunctorCat PointedCGWH.{u, v} I)
      PointedCGWH.{u, v} SSet.{v}).obj singularFunctor

/-- Both bifunctors have the same entire original singular mapping object at every pair. -/
theorem mappingFunctor_obj (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X).obj Y =
      ((singularMappingFunctor (I := I)).obj X).obj Y := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire simplicial mapping bifunctor keeps both original variance functions. -/
def mappingFunctorIso :
    SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      singularMappingFunctor (I := I) :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => eqToIso (mappingFunctor_obj X Y)) (fun f => by
      change eHomWhiskerLeft SSet.{v} X.unop f ≫ 𝟙 _ =
        𝟙 _ ≫ singularFunctor.map (EnrichedFunctorCat.WeightedEndVariance.post X.unop f)
      rw [Category.comp_id, Category.id_comp]
      exact target_map X.unop f))
    (fun f => by
      apply NatTrans.ext
      funext Y
      change eHomWhiskerRight SSet.{v} f.unop Y ≫ 𝟙 _ =
        𝟙 _ ≫ singularFunctor.map (EnrichedFunctorCat.WeightedEndVariance.pre f.unop Y)
      rw [Category.comp_id, Category.id_comp]
      exact source_map f.unop Y)

/-- Every forward object component is the original identity of the complete singular mapping end. -/
theorem mappingFunctorIso_hom_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((mappingFunctorIso (I := I)).hom.app X).app Y =
      𝟙 (singularFunctor.obj (PointedCGWH.EnrichedFunctorMapping.mappingObject X.unop Y)) := rfl

/-- Every inverse object component is the same original complete singular identity function. -/
theorem mappingFunctorIso_inv_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((mappingFunctorIso (I := I)).inv.app X).app Y =
      𝟙 (singularFunctor.obj (PointedCGWH.EnrichedFunctorMapping.mappingObject X.unop Y)) := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.SimplicialEnrichment
