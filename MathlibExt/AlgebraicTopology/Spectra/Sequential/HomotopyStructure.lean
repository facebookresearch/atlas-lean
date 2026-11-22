/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift
import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Omega

/-!
# The actual original spectrum structure maps on cube homotopy and groups

The existing original enriched spectrum evaluations, one-sphere structure
maps and adjoint structure maps are retained. The genuine native loop
homotopy shift gives full all-degree cube and positive group structure-map
natural transformations on the original spectrum category.

Every whole original spectrum map and every actual source/target level is
preserved. The group function is exactly the all-degree cube function in
its actual positive degree. These transformations supply structure maps
for the original varying-degree construction without defining a second
stable-pi protocol or assuming a suspension-colimit law.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.NativeLoopShiftGeometry

/-- The entire original level cube homotopy functor in every actual degree. -/
def levelCubePiFunctor (n k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤ Type v :=
  PointedCGWH.SequentialSpectrum.evaluation n ⋙ PointedCGWH.piNFunctor k

/-- The entire original level positive cube group functor. -/
def levelCubeGroupFunctor (n k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤ GrpCat.{v} :=
  PointedCGWH.SequentialSpectrum.evaluation n ⋙ PointedCGWH.piNPositiveFunctor k

/-- The same original successor transpose is the whole pointed level natural transformation. -/
def adjointStructureNatTrans (n : ℕ) :
    PointedCGWH.SequentialSpectrum.evaluation.{u, v} n ⟶
      PointedCGWH.SequentialSpectrum.evaluation (n + 1) ⋙ PointedCGWH.loop where
  app X := PointedCGWH.SequentialSpectrum.adjointStructureMap X n
  naturality {X Y} f :=
    PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality (X := X) (Y := Y) f n

/-- Every entire original transpose component is the exact original
spectrum adjoint structure map. -/
theorem adjointStructureNatTrans_app (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (adjointStructureNatTrans n).app X =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X n := rfl

/-- The whole actual transpose retains the original uncurried one-sphere structure map. -/
theorem adjointStructureNatTrans_uncurry (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    MonoidalClosed.uncurry ((adjointStructureNatTrans n).app X) =
      PointedCGWH.SequentialSpectrum.structureMap X n :=
  PointedCGWH.SequentialSpectrum.adjointStructureMap_uncurry X n

/-- The actual native cube shift constructs the whole original spectrum homotopy structure map. -/
def cubeStructureNatTrans (n k : ℕ) :
    levelCubePiFunctor.{u, v} n k ⟶ levelCubePiFunctor (n + 1) (k + 1) :=
  Functor.whiskerRight (adjointStructureNatTrans n) (PointedCGWH.piNFunctor k) ≫
    (Functor.isoWhiskerLeft (PointedCGWH.SequentialSpectrum.evaluation (n + 1))
      (nativeLoopPiShiftNatIso k)).hom

/-- The actual native group shift constructs the whole original positive structure group map. -/
def groupStructureNatTrans (n k : ℕ) :
    levelCubeGroupFunctor.{u, v} n k ⟶ levelCubeGroupFunctor (n + 1) (k + 1) :=
  Functor.whiskerRight (adjointStructureNatTrans n) (PointedCGWH.piNPositiveFunctor k) ≫
    (Functor.isoWhiskerLeft (PointedCGWH.SequentialSpectrum.evaluation (n + 1))
      (nativeLoopGroupShiftNatIso k)).hom

/-- The whole original cube structure function is exactly the original transpose and loop shift. -/
theorem cubeStructureNatTrans_app (n k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (q : PointedCGWH.piN k (X.level n)) :
    (cubeStructureNatTrans n k).app X q =
      (nativeLoopPiShiftNatIso k).hom.app (X.level (n + 1))
        (PointedCGWH.piNMap k (PointedCGWH.SequentialSpectrum.adjointStructureMap X n) q) := rfl

/-- The whole original group structure function is exactly the original
group transpose and shift. -/
theorem groupStructureNatTrans_app (n k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (q : PointedCGWH.piN (k + 1) (X.level n)) :
    ((groupStructureNatTrans n k).app X).hom q =
      ((nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1))).hom
        ((PointedCGWH.piNPositiveMap k
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X n)).hom q) := rfl

/-- The actual group structure function is the same cube function
in its original positive degree. -/
theorem groupStructureNatTrans_eq_cube (n k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (q : PointedCGWH.piN (k + 1) (X.level n)) :
    ((groupStructureNatTrans n k).app X).hom q = (cubeStructureNatTrans n (k + 1)).app X q :=
  (congrArg ((nativeLoopGroupShiftNatIso k).hom.app (X.level (n + 1))).hom
      (PointedCGWH.piNPositiveMap_apply k
        (PointedCGWH.SequentialSpectrum.adjointStructureMap X n) q)).trans
    (nativeLoopGroupShiftNatIso_hom_eq_allDegree k (X.level (n + 1)) _)

/-- Every whole original spectrum map retains all source/target cube structure naturalities. -/
theorem cubeStructureNatTrans_naturality (n k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (levelCubePiFunctor n k).map f ≫ (cubeStructureNatTrans n k).app Y =
      (cubeStructureNatTrans n k).app X ≫ (levelCubePiFunctor (n + 1) (k + 1)).map f :=
  (cubeStructureNatTrans n k).naturality f

/-- Every whole original spectrum map retains all source/target group structure naturalities. -/
theorem groupStructureNatTrans_naturality (n k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (levelCubeGroupFunctor n k).map f ≫ (groupStructureNatTrans n k).app Y =
      (groupStructureNatTrans n k).app X ≫ (levelCubeGroupFunctor (n + 1) (k + 1)).map f :=
  (groupStructureNatTrans n k).naturality f

end PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
