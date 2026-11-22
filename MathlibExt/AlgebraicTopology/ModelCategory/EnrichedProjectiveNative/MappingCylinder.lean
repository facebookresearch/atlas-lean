/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Interval
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative

/-!
# Literal mapping cylinders on the actual native diagram category

The original native projective constructor at the caller's original bottom
supplies finite colimits. The mapping cylinder is the actual pushout along
the original first interval inclusion. The source uses the second inclusion;
retraction uses the original contraction. All whole Arrow maps, naturalities,
the target section and literal factorization are retained. This file does
not assert cylinder model classes, K acyclicity or localization existence.

The native factory has its supported legacy importing route.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedIntervalCylinder
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedIntervalMappingCylinder

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

/-- The actual native mapping cylinder uses the same original first inclusion and caller arrow. -/
abbrev object (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  pushout (inclusion 0 f.left) f.hom

/-- The original interval leg of the actual native pushout. -/
abbrev intervalLeg (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    EnrichedIntervalCylinder.object f.left ⟶ object f :=
  pushout.inl (inclusion 0 f.left) f.hom

/-- The original target leg of the actual native pushout. -/
abbrev targetLeg (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    f.right ⟶ object f := pushout.inr (inclusion 0 f.left) f.hom

/-- The factorization source uses the actual second original interval endpoint. -/
def source (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) : f.left ⟶ object f :=
  inclusion 1 f.left ≫ intervalLeg f

/-- The retraction is the actual pushout descent of the original contraction and target identity. -/
def retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) : object f ⟶ f.right :=
  pushout.desc (projection f.left ≫ f.hom) (𝟙 f.right) (by
    rw [← Category.assoc, inclusion_projection, Category.id_comp, Category.comp_id])

omit B in
/-- The whole interval leg of retraction keeps the original contraction followed by f. -/
@[reassoc]
theorem intervalLeg_retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    intervalLeg f ≫ retraction f = projection f.left ≫ f.hom :=
  pushout.inl_desc _ _ _

omit B in
/-- The original target leg is a section of the actual same retraction. -/
@[reassoc]
theorem targetLeg_retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    targetLeg f ≫ retraction f = 𝟙 f.right := pushout.inr_desc _ _ _

omit B in
/-- The literal original caller arrow factors through the second original endpoint. -/
@[reassoc]
theorem fac (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    source f ≫ retraction f = f.hom := by
  rw [source, Category.assoc, intervalLeg_retraction,
    ← Category.assoc, inclusion_projection, Category.id_comp]

/-- An arbitrary whole original Arrow map induces the actual corresponding pushout map. -/
def map {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    object f ⟶ object g :=
  pushout.desc
    (tensorLeftMap IntervalCoefficient.interval h.left ≫ intervalLeg g)
    (h.right ≫ targetLeg g) (by
      rw [← Category.assoc, inclusion_naturality, Category.assoc,
        pushout.condition, ← Category.assoc, Arrow.w h, Category.assoc])

omit B in
/-- Every induced pushout map retains the entire genuine tensor action on the original left map. -/
@[reassoc]
theorem intervalLeg_map {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    intervalLeg f ≫ map h = tensorLeftMap IntervalCoefficient.interval h.left ≫ intervalLeg g :=
  pushout.inl_desc _ _ _

omit B in
/-- Every induced pushout map retains the original full right Arrow map. -/
@[reassoc]
theorem targetLeg_map {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    targetLeg f ≫ map h = h.right ≫ targetLeg g := pushout.inr_desc _ _ _

omit B in
/-- The entire source factorization map is natural in the actual original Arrow morphism. -/
@[reassoc]
theorem source_map {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    source f ≫ map h = h.left ≫ source g := by
  rw [source, source, Category.assoc, intervalLeg_map,
    ← Category.assoc, inclusion_naturality, Category.assoc]

omit B in
/-- The whole original retraction is natural in every actual original Arrow map. -/
@[reassoc]
theorem map_retraction {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    map h ≫ retraction g = retraction f ≫ h.right := by
  apply pushout.hom_ext
  · rw [← Category.assoc, intervalLeg_map, Category.assoc, intervalLeg_retraction,
      intervalLeg_retraction_assoc, ← Category.assoc, projection_naturality,
      Category.assoc, Arrow.w h]
  · rw [← Category.assoc, targetLeg_map, Category.assoc, targetLeg_retraction,
      Category.comp_id, ← Category.assoc, targetLeg_retraction, Category.id_comp]

/-- The literal mapping-cylinder construction is a genuine functor on the whole Arrow category. -/
def functor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I where
  obj f := object f
  map h := map h
  map_id f := by
    apply pushout.hom_ext
    · rw [intervalLeg_map, Arrow.id_left, Category.comp_id]
      change (EnrichedFunctorCat.tensorLeft IntervalCoefficient.interval).map (𝟙 f.left) ≫
        intervalLeg f = intervalLeg f
      rw [CategoryTheory.Functor.map_id]
      change 𝟙 (EnrichedIntervalCylinder.object f.left) ≫ intervalLeg f = intervalLeg f
      rw [Category.id_comp]
    · rw [targetLeg_map, Arrow.id_right, Category.id_comp, Category.comp_id]
  map_comp h k := by
    apply pushout.hom_ext
    · rw [intervalLeg_map, ← Category.assoc, intervalLeg_map,
        Category.assoc, intervalLeg_map, Arrow.comp_left]
      change (EnrichedFunctorCat.tensorLeft IntervalCoefficient.interval).map
          (h.left ≫ k.left) ≫ intervalLeg _ =
        (EnrichedFunctorCat.tensorLeft IntervalCoefficient.interval).map h.left ≫
          (EnrichedFunctorCat.tensorLeft IntervalCoefficient.interval).map k.left ≫ intervalLeg _
      rw [CategoryTheory.Functor.map_comp]
      exact Category.assoc _ _ _
    · rw [targetLeg_map, ← Category.assoc, targetLeg_map,
        Category.assoc, targetLeg_map, Arrow.comp_right]
      exact Category.assoc _ _ _

/-- The original second-endpoint source maps form a genuine natural transformation. -/
def sourceNatTrans : Arrow.leftFunc ⟶ functor (I := I) where
  app f := source f
  naturality _ _ h := (source_map h).symm

/-- The original same retractions form a genuine natural transformation. -/
def retractionNatTrans : functor (I := I) ⟶ Arrow.rightFunc where
  app f := retraction f
  naturality _ _ h := map_retraction h

omit B in
/-- The factorization holds as a whole natural transformation on all original Arrow data. -/
theorem fac_natTrans : sourceNatTrans (I := I) ≫ retractionNatTrans =
    Arrow.leftToRight := by
  apply NatTrans.ext
  funext f
  exact fac f

end PointedCGWH.EnrichedIntervalMappingCylinder
