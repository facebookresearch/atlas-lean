/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKSourceLoopClassTransport

/-!
# The actual scalar suspension unit on native sequential spectra

The suspension and loop functors are the original scalar tensor and cotensor
by the native one-sphere, on the unchanged enriched sequential carrier. Their
unit and counit have the literal closed-category component formulas.

The positive suspension maps use this actual unit and the original native
loop-group shift. Composing with the original spectrum structure map gives
the original varying-degree transition. Every integer unit map is the map
of the same original filtered group quotient; no invertibility is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry

open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.NativeLoopShiftGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Scalar suspension is the actual pointwise left tensor with the native one-sphere. -/
abbrev suspension : SequentialSpectrum.{u, v} ⥤ SequentialSpectrum.{u, v} :=
  EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne

/-- Scalar loops are the actual pointwise native one-sphere internal Hom. -/
abbrev loop : SequentialSpectrum.{u, v} ⥤ SequentialSpectrum.{u, v} :=
  EnrichedFunctorCat.cotensor PointedCGWH.sphereOne

/-- The scalar adjunction retains the original enriched tensor and cotensor maps. -/
abbrev adjunction : suspension.{u, v} ⊣ loop :=
  ScalarLeibniz.adjunction PointedCGWH.sphereOne

/-- The actual unit is a genuine enriched spectrum transformation on every input. -/
abbrev unit : 𝟭 SequentialSpectrum.{u, v} ⟶ suspension ⋙ loop := adjunction.unit

/-- The actual counit is the original pointwise closed evaluation. -/
abbrev counit : loop.{u, v} ⋙ suspension ⟶ 𝟭 SequentialSpectrum := adjunction.counit

/-- Each original suspension value is the native left smash, with no replacement of the level. -/
theorem suspension_obj_level (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    (suspension.obj X).level n = PointedCGWH.sphereOne ⊗ X.level n := rfl

/-- The whole original spectrum component is literally left-whiskered by the one-sphere. -/
theorem suspension_map_levelMap {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    levelMap (suspension.map f) n = PointedCGWH.sphereOne ◁ levelMap f n :=
  tensorLeftMap_component PointedCGWH.sphereOne f _

/-- Each original loop value is the actual based internal Hom from the native one-sphere. -/
theorem loop_obj_level (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    (loop.obj X).level n = PointedCGWH.loop.obj (X.level n) := rfl

/-- The complete original input map acts by the actual based internal-Hom map. -/
theorem loop_map_levelMap {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    levelMap (loop.map f) n = PointedCGWH.loop.map (levelMap f n) :=
  cotensorMap_component PointedCGWH.sphereOne f _

set_option backward.isDefEq.respectTransparency false in
/-- The full scalar-unit level map is the literal curry of the tensor identity. -/
theorem unit_levelMap (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    levelMap (unit.app X) n =
      MonoidalClosed.curry (𝟙 (PointedCGWH.sphereOne ⊗ X.level n)) := by
  change component
      (ScalarLeibniz.adjunct PointedCGWH.sphereOne X (suspension.obj X)
        (𝟙 (suspension.obj X))) _ = _
  rw [ScalarLeibniz.adjunct_component]
  exact congrArg MonoidalClosed.curry
    (EnrichedFunctorCat.component_id (suspension.obj X)
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))

/-- Uncurrying the entire scalar-unit component recovers the original tensor identity. -/
theorem unit_levelMap_uncurry (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    MonoidalClosed.uncurry (levelMap (unit.app X) n) =
      𝟙 (PointedCGWH.sphereOne ⊗ X.level n) := by
  rw [unit_levelMap, MonoidalClosed.uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
/-- Each complete counit component is the original based closed evaluation. -/
theorem counit_levelMap (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    levelMap (counit.app X) n =
      MonoidalClosed.uncurry (𝟙 (PointedCGWH.loop.obj (X.level n))) := by
  change component
      (ScalarLeibniz.unadjunct PointedCGWH.sphereOne (loop.obj X) X
        (𝟙 (loop.obj X))) _ = _
  rw [ScalarLeibniz.unadjunct_component, component_id]
  rfl

/-- The actual original input components commute with the entire scalar-unit component. -/
theorem unit_levelMap_naturality {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    levelMap f n ≫ levelMap (unit.app Y) n =
      levelMap (unit.app X) n ≫
        PointedCGWH.loop.map (PointedCGWH.sphereOne ◁ levelMap f n) := by
  have h := congrArg (fun g => levelMap g n) (unit.naturality f)
  change levelMap (f ≫ unit.app Y) n =
    levelMap (unit.app X ≫ loop.map (suspension.map f)) n at h
  rw [levelMap_comp, levelMap_comp, loop_map_levelMap, suspension_map_levelMap] at h
  exact h

/-- The actual unit retains naturality on the entire original enriched index Hom. -/
theorem unit_full_naturality (X : SequentialSpectrum.{u, v})
    (a b : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b) ≫ component (unit.app X) b =
      (component (unit.app X) a ⊗ₘ 𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        MonoidalClosed.uncurry (((suspension ⋙ loop).obj X).toEnrichedFunctor.map a b) :=
  (unit.app X).uncurriedNaturality a b

/-- The unit and counit satisfy the entire original left triangle. -/
theorem left_triangle (X : SequentialSpectrum.{u, v}) :
    suspension.map (unit.app X) ≫ counit.app (suspension.obj X) =
      𝟙 (suspension.obj X) := adjunction.left_triangle_components X

/-- The unit and counit satisfy the entire original right triangle. -/
theorem right_triangle (X : SequentialSpectrum.{u, v}) :
    unit.app (loop.obj X) ≫ loop.map (counit.app X) = 𝟙 (loop.obj X) :=
  adjunction.right_triangle_components X

/-- The original structure transpose factors through the actual scalar unit. -/
theorem unit_levelMap_structureMap (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    levelMap (unit.app X) n ≫ PointedCGWH.loop.map (X.structureMap n) =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X n := by
  rw [unit_levelMap]
  change MonoidalClosed.curry (𝟙 (PointedCGWH.sphereOne ⊗ X.level n)) ≫
    (ihom PointedCGWH.sphereOne).map (X.structureMap n) = _
  rw [← MonoidalClosed.curry_natural_right, Category.id_comp]
  rfl

/-- Every positive level group uses the existing original native loop-group comparison. -/
abbrev loopGroupEvaluationIso (n k : ℕ) :
    loop.{u, v} ⋙ levelCubeGroupFunctor n k ≅ levelCubeGroupFunctor n (k + 1) :=
  HomotopicalAlgebra.EnrichedProjective.Native.SourceLoopClassTransport.scalarLoopGroupEvaluationIso
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n) k

/-- The evaluation comparison's forward component is the original native group shift. -/
theorem loopGroupEvaluationIso_hom_app (n k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (loopGroupEvaluationIso n k).hom.app X =
      (nativeLoopGroupShiftNatIso k).hom.app (X.level n) := by
  change (piNPositiveFunctor k).map (𝟙 _) ≫ 𝟙 _ ≫
    (nativeLoopGroupShiftNatIso k).hom.app (X.level n) = _
  rw [(piNPositiveFunctor k).map_id, Category.id_comp, Category.id_comp]

/-- The actual level suspension group map is the scalar unit followed by the native loop shift. -/
def suspensionGroupMap (n k : ℕ) : levelCubeGroupFunctor.{u, v} n k ⟶
    suspension ⋙ levelCubeGroupFunctor n (k + 1) :=
  Functor.whiskerRight unit (levelCubeGroupFunctor n k) ≫
    (Functor.associator suspension loop (levelCubeGroupFunctor n k)).hom ≫
    (Functor.isoWhiskerLeft suspension (loopGroupEvaluationIso n k)).hom

/-- Each whole forward group component keeps the original coevaluation and native group shift. -/
theorem suspensionGroupMap_app (n k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (suspensionGroupMap n k).app X =
      (piNPositiveFunctor k).map (levelMap (unit.app X) n) ≫
        (nativeLoopGroupShiftNatIso k).hom.app ((suspension.obj X).level n) := by
  change (piNPositiveFunctor k).map (levelMap (unit.app X) n) ≫ 𝟙 _ ≫
    (loopGroupEvaluationIso n k).hom.app (suspension.obj X) = _
  rw [Category.id_comp, loopGroupEvaluationIso_hom_app]

/-- Every original cube class retains the actual scalar-unit class and full native shift. -/
theorem suspensionGroupMap_apply (n k : ℕ) (X : SequentialSpectrum.{u, v})
    (a : piN (k + 1) (X.level n)) :
    ((suspensionGroupMap n k).app X).hom a =
      ((nativeLoopGroupShiftNatIso k).hom.app ((suspension.obj X).level n)).hom
        (piNMap (k + 1) (levelMap (unit.app X) n) a) := by
  rw [suspensionGroupMap_app]
  exact congrArg ((nativeLoopGroupShiftNatIso k).hom.app ((suspension.obj X).level n)).hom
    (piNPositiveMap_apply k (levelMap (unit.app X) n) a)

/-- The reverse level group map is induced by the original entire spectrum structure map. -/
def suspensionStructureGroupMap (n k : ℕ) :
    suspension.{u, v} ⋙ levelCubeGroupFunctor n (k + 1) ⟶
      levelCubeGroupFunctor (n + 1) (k + 1) where
  app X := (piNPositiveFunctor (k + 1)).map (X.structureMap n)
  naturality X Y f := by
    change (piNPositiveFunctor (k + 1)).map (levelMap (suspension.map f) n) ≫
        (piNPositiveFunctor (k + 1)).map (Y.structureMap n) =
      (piNPositiveFunctor (k + 1)).map (X.structureMap n) ≫
        (piNPositiveFunctor (k + 1)).map (levelMap f (n + 1))
    rw [suspension_map_levelMap, ← Functor.map_comp, ← Functor.map_comp]
    exact (piNPositiveFunctor (k + 1)).congr_map (structureMap_naturality f n)

/-- Both complete level group maps factor the actual original varying-degree structure map. -/
theorem suspensionGroupMap_comp_structure (n k : ℕ) :
    suspensionGroupMap.{u, v} n k ≫ suspensionStructureGroupMap n k =
      groupStructureNatTrans n k := by
  apply NatTrans.ext
  funext X
  change (suspensionGroupMap n k).app X ≫
    (piNPositiveFunctor (k + 1)).map (X.structureMap n) = _
  rw [suspensionGroupMap_app]
  let a : X.level n ⟶ PointedCGWH.loop.obj (PointedCGWH.sphereOne ⊗ X.level n) :=
    levelMap (unit.app X) n
  let s : PointedCGWH.sphereOne ⊗ X.level n ⟶ X.level (n + 1) := X.structureMap n
  change ((piNPositiveFunctor k).map a ≫
      (nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.sphereOne ⊗ X.level n)) ≫
        (piNPositiveFunctor (k + 1)).map s =
    (piNPositiveFunctor k).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X n) ≫
      (nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1))
  have hs := (nativeLoopGroupShiftNatIso k).hom.naturality s
  have ha : a ≫ PointedCGWH.loop.map s =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X n :=
    unit_levelMap_structureMap X n
  calc
    _ = (piNPositiveFunctor k).map a ≫
        ((piNPositiveFunctor k).map (PointedCGWH.loop.map s) ≫
          (nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1))) :=
      (Category.assoc _ _ _).trans (congrArg (fun z => (piNPositiveFunctor k).map a ≫ z) hs.symm)
    _ = (piNPositiveFunctor k).map (a ≫ PointedCGWH.loop.map s) ≫
        (nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1)) :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun z => z ≫ (nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1)))
        ((piNPositiveFunctor k).map_comp a (PointedCGWH.loop.map s)).symm)
    _ = _ := congrArg
      (fun z => (piNPositiveFunctor k).map z ≫
        (nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1))) ha

/-- The scalar unit induces the actual original group-quotient map in every integer degree. -/
def integerUnitMap (q : ℤ) : integerStablePiFunctor.{u, v} q ⟶
    (suspension ⋙ loop) ⋙ integerStablePiFunctor q :=
  Functor.whiskerRight unit (integerStablePiFunctor q)

/-- Every whole integer-unit component is the original filtered group colimit map. -/
theorem integerUnitMap_app (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    (integerUnitMap q).app X =
      GrpCat.FilteredColimits.colimitMap ((integerDiagonalDiagramFunctor q).map (unit.app X)) :=
  rfl

/-- Every original integer quotient leg retains the actual unit at its original level and degree. -/
theorem integerUnitMap_leg (q : ℤ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg q X n ≫ (integerUnitMap q).app X =
      (piNPositiveFunctor (integerTailPositiveIndex q + n)).map
          (levelMap (unit.app X) (integerTailLevel q + n)) ≫
        integerStablePiLeg q ((suspension ⋙ loop).obj X) n :=
  integerStablePiLeg_naturality q (unit.app X) n

end PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionGeometry
