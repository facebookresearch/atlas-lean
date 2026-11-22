/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Omega
import MathlibExt.AlgebraicTopology.Spectra.Sequential.EnrichedPresentation
import MathlibExt.AlgebraicTopology.Spectra.Sequential.Closed

/-!
# The original ordered loop-successor construction and its full unit

The successor loop objects carry the structure obtained by uncurrying
the loop of the original successor transpose. Its whole functor and
natural unit retain the actual original successor maps. The construction
is carried to the SAME enriched spectrum carrier through the complete
original reconstruction equivalence, including all original Hom actions.
The literal identification with the MMSS free function spectrum remains
a separate source obligation; no sphere self-interchange law is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.SequentialSpectrum.EnrichedPresentation
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.SequentialSpectrum.OrderedLoop
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- Every successor loop keeps the original successor transpose in its actual structure. -/
def object (K : C) (X : SequentialSpectrum C K) : SequentialSpectrum C K where
  level n := (ihom K).obj (X.level (n + 1))
  structureMap n := MonoidalClosed.uncurry ((ihom K).map (adjointStructureMap X (n + 1)))

/-- Every original complete input morphism acts by its literal looped successor component. -/
def map (K : C) {X Y : SequentialSpectrum C K} (f : X ⟶ Y) : object K X ⟶ object K Y where
  levelMap n := (ihom K).map (f.levelMap (n + 1))
  naturality n := by
    dsimp only [object]
    apply MonoidalClosed.curry_injective
    rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_uncurry,
      MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry,
      ← Functor.map_comp, ← Functor.map_comp, adjointStructureMap_naturality]

/-- The complete original loop-successor construction satisfies identity and composition. -/
def functor (K : C) : SequentialSpectrum C K ⥤ SequentialSpectrum C K where
  obj := object K
  map := map K
  map_id X := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact (ihom K).map_id (X.level (n + 1))
  map_comp f g := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact (ihom K).map_comp (f.levelMap (n + 1)) (g.levelMap (n + 1))

/-- The actual successor transpose of this construction is the loop of the original transpose. -/
theorem adjointStructureMap_object (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    adjointStructureMap (object K X) n = (ihom K).map (adjointStructureMap X (n + 1)) :=
  MonoidalClosed.curry_uncurry _

/-- The unit is the ENTIRE original successor-transpose family with genuine structure naturality. -/
def unitApp (K : C) (X : SequentialSpectrum C K) : X ⟶ object K X where
  levelMap n := adjointStructureMap X n
  naturality n := by
    dsimp only [object]
    apply MonoidalClosed.curry_injective
    rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_uncurry,
      MonoidalClosed.curry_natural_right]
    rfl

/-- All original spectrum maps commute with the whole original ordered unit. -/
def unit (K : C) : 𝟭 (SequentialSpectrum C K) ⟶ functor K where
  app := unitApp K
  naturality {X Y} f := by
    apply SequentialSpectrum.hom_ext
    intro n
    exact adjointStructureMap_naturality f n

/-- Every original unit component is retained as the literal original successor transpose. -/
theorem unitApp_levelMap (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    (unitApp K X).levelMap n = adjointStructureMap X n := rfl

/--
Looping the whole unit in the original order is exactly its unit at the loop-successor object.
-/
theorem map_unitApp (K : C) (X : SequentialSpectrum C K) :
    (functor K).map (unitApp K X) = unitApp K ((functor K).obj X) := by
  apply SequentialSpectrum.hom_ext
  intro n
  exact (adjointStructureMap_object K X n).symm

/-- Every original levelwise unit condition is precisely the given original Omega condition. -/
theorem unitApp_level_property_iff (K : C) (W : MorphismProperty C)
    (X : SequentialSpectrum C K) :
    (∀ n : ℕ, W ((unitApp K X).levelMap n)) ↔
      CategoryTheory.SequentialSpectrum.IsOmega W X := Iff.rfl

end CategoryTheory.SequentialSpectrum.OrderedLoop

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private theorem reconstructedAdjointStructureMap
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasInitial C]
    (K : C) (X : CategoryTheory.SequentialSpectrum C K) (n : ℕ) :
    CategoryTheory.Spectra.Sequential.adjointStructureMap
        ((toEnrichedFunctors K).obj X) n =
      CategoryTheory.SequentialSpectrum.adjointStructureMap X n := by
  change MonoidalClosed.curry
    ((fromEnrichedFunctor K (toEnrichedFunctor K X)).structureMap n) = _
  rw [from_to_structureMap]
  rfl

private theorem reconstructedComponent
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasInitial C]
    (K : C) {X Y : CategoryTheory.SequentialSpectrum C K} (f : X ⟶ Y) (n : ℕ) :
    CategoryTheory.Spectra.Sequential.levelMap ((toEnrichedFunctors K).map f) n =
      f.levelMap n :=
  toEnrichedFunctorMap_component K f (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)

private theorem reconstructedUnitComponent
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasInitial C]
    (K : C) (X : Carrier K) (n : ℕ) :
    component
      ((enrichedCounitIsoApp K X).inv ≫
        toEnrichedFunctorMap K
          (CategoryTheory.SequentialSpectrum.OrderedLoop.unitApp K
            ((fromEnrichedFunctors K).obj X)))
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) =
        CategoryTheory.Spectra.Sequential.adjointStructureMap X n := by
  exact (component_comp
    (enrichedCounitIsoApp K X).inv
    (toEnrichedFunctorMap K
      (CategoryTheory.SequentialSpectrum.OrderedLoop.unitApp K
        ((fromEnrichedFunctors K).obj X)))
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)).trans
    ((congrArg₂ (fun f g => f ≫ g)
      (enrichedCounitIsoApp_inv_component K X n)
      (toEnrichedFunctorMap_component K
        (CategoryTheory.SequentialSpectrum.OrderedLoop.unitApp K
          ((fromEnrichedFunctors K).obj X))
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n))).trans
      (Category.id_comp _))

namespace PointedCGWH.SequentialSpectrum.OrderedLoop
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The whole loop-successor functor uses the SAME complete original reconstruction functors. -/
def functor : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  fromEnrichedFunctors PointedCGWH.sphereOne ⋙
    CategoryTheory.SequentialSpectrum.OrderedLoop.functor PointedCGWH.sphereOne ⋙
      toEnrichedFunctors PointedCGWH.sphereOne

/-- Every level of the complete native output is the actual original successor loop object. -/
theorem functor_obj_level (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (functor.obj X).level n = (ihom PointedCGWH.sphereOne).obj (X.level (n + 1)) := rfl

/-- Reconstruction retains the actual original successor transpose before applying the loop. -/
theorem from_adjointStructureMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    CategoryTheory.SequentialSpectrum.adjointStructureMap
        ((fromEnrichedFunctors PointedCGWH.sphereOne).obj X) n =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X n := rfl

/-- The native full structure map is the original uncurried looped successor transpose. -/
theorem functor_structureMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.structureMap (functor.obj X) n =
      MonoidalClosed.uncurry
        ((ihom PointedCGWH.sphereOne).map
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X (n + 1))) := by
  change (fromEnrichedFunctor PointedCGWH.sphereOne
    (toEnrichedFunctor PointedCGWH.sphereOne
      ((CategoryTheory.SequentialSpectrum.OrderedLoop.functor PointedCGWH.sphereOne).obj
        ((fromEnrichedFunctors PointedCGWH.sphereOne).obj X)))).structureMap n = _
  rw [from_to_structureMap]
  rfl

/-- Every native successor transpose is the loop of the SAME original successor transpose. -/
theorem functor_adjointStructureMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.adjointStructureMap (functor.obj X) n =
      (ihom PointedCGWH.sphereOne).map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap X (n + 1)) :=
  (reconstructedAdjointStructureMap PointedCGWH.sphereOne
    ((CategoryTheory.SequentialSpectrum.OrderedLoop.functor PointedCGWH.sphereOne).obj
      ((fromEnrichedFunctors PointedCGWH.sphereOne).obj X)) n).trans
    ((CategoryTheory.SequentialSpectrum.OrderedLoop.adjointStructureMap_object
      PointedCGWH.sphereOne _ n).trans
      (congrArg (ihom PointedCGWH.sphereOne).map (from_adjointStructureMap X (n + 1))))

/-- Every actual native map keeps the loop of its SAME original successor component. -/
theorem functor_map_levelMap
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (functor.map f) n =
      (ihom PointedCGWH.sphereOne).map
        (PointedCGWH.SequentialSpectrum.levelMap f (n + 1)) :=
  reconstructedComponent PointedCGWH.sphereOne
    ((CategoryTheory.SequentialSpectrum.OrderedLoop.functor PointedCGWH.sphereOne).map
      ((fromEnrichedFunctors PointedCGWH.sphereOne).map f)) n

/-- The whole input-map component family retains ALL original natural-number degrees. -/
theorem functor_map_components
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (fun n : ℕ => PointedCGWH.SequentialSpectrum.levelMap (functor.map f) n) =
      (fun n : ℕ => (ihom PointedCGWH.sphereOne).map
        (PointedCGWH.SequentialSpectrum.levelMap f (n + 1))) := by
  funext n
  exact functor_map_levelMap f n

/-- Every whole original enriched source Hom action of the native output is retained. -/
theorem functor_uncurry_action
    (X : PointedCGWH.SequentialSpectrum.{u, v})
    (a b : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    MonoidalClosed.uncurry ((functor.obj X).toEnrichedFunctor.map a b) =
      spectrumAction
        ((CategoryTheory.SequentialSpectrum.OrderedLoop.functor PointedCGWH.sphereOne).obj
          ((fromEnrichedFunctors PointedCGWH.sphereOne).obj X)) a b :=
  toEnrichedFunctor_uncurry_map PointedCGWH.sphereOne _ a b

/-- The ENTIRE native unit uses the original full inverse counit and full reconstruction maps. -/
def unit : 𝟭 PointedCGWH.SequentialSpectrum.{u, v} ⟶ functor :=
  (enrichedCounitIso PointedCGWH.sphereOne).inv ≫
    CategoryTheory.Functor.whiskerLeft
      (fromEnrichedFunctors PointedCGWH.sphereOne)
      (CategoryTheory.Functor.whiskerRight
        (CategoryTheory.SequentialSpectrum.OrderedLoop.unit PointedCGWH.sphereOne)
        (toEnrichedFunctors PointedCGWH.sphereOne))

/-- Every native unit component is the SAME original successor transpose. -/
theorem unit_levelMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (unit.app X) n =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X n :=
  reconstructedUnitComponent PointedCGWH.sphereOne X n

/-- Every complete original native map commutes with the whole native unit. -/
theorem unit_naturality
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    f ≫ unit.app Y = unit.app X ≫ functor.map f := unit.naturality f

/-- The entire original native unit component function retains ALL original degrees. -/
theorem unit_components (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (fun n : ℕ => PointedCGWH.SequentialSpectrum.levelMap (unit.app X) n) =
      (fun n : ℕ => PointedCGWH.SequentialSpectrum.adjointStructureMap X n) := by
  funext n
  exact unit_levelMap X n

/-- Actual native Omega objects are exactly those whose actual native unit is level weak. -/
theorem unit_level_weak_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (∀ n : ℕ, CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.levelMap (unit.app X) n).right) ↔ X.IsOmega := by
  simp only [unit_levelMap]
  rfl

end PointedCGWH.SequentialSpectrum.OrderedLoop
