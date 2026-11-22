/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.HomotopyStructure
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Evaluation

/-!
# The actual original ordered loop iteration on homotopy groups

The frozen original `loopPower`, ordered iteration, full evaluation Iso
and exact original iterate units are retained. Iterating the genuine native
group loop shift gives the full homotopy-group comparison for every
original iterate and level, with both component maps and every complete
original spectrum-map naturality.

The actual original iterate unit is identified on groups with the original
adjoint structure map. No function-spectrum identification, telescope
homotopy comparison or stable-pi law is supplied or claimed.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry

/-- All original loop powers have the full original positive cube group shift. -/
def loopPowerGroupShiftNatIso : ∀ n k : ℕ,
    loopPower.{u, v} n ⋙ PointedCGWH.piNPositiveFunctor k ≅
      PointedCGWH.piNPositiveFunctor (k + n) :=
  Nat.rec
    (motive := fun n => ∀ k : ℕ,
      loopPower.{u, v} n ⋙ PointedCGWH.piNPositiveFunctor k ≅
        PointedCGWH.piNPositiveFunctor (k + n))
    (fun k => (PointedCGWH.piNPositiveFunctor k).leftUnitor)
    (fun n previous k =>
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNPositiveFunctor k) ≪≫
        Functor.isoWhiskerLeft (loopPower n) (nativeLoopGroupShiftNatIso k) ≪≫
          previous (k + 1) ≪≫
            eqToIso (congrArg PointedCGWH.piNPositiveFunctor
              (show k + 1 + n = k + (n + 1) by omega)))

/-- The whole structural successor keeps the original native shift and both complete Iso maps. -/
theorem loopPowerGroupShiftNatIsoSucc (n k : ℕ) :
    loopPowerGroupShiftNatIso.{u, v} (n + 1) k =
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNPositiveFunctor k) ≪≫
        Functor.isoWhiskerLeft (loopPower n) (nativeLoopGroupShiftNatIso k) ≪≫
          loopPowerGroupShiftNatIso n (k + 1) ≪≫
            eqToIso (congrArg PointedCGWH.piNPositiveFunctor
              (show k + 1 + n = k + (n + 1) by omega)) := rfl

/-- The original whole zero group shift is its actual group-functor left unitor. -/
theorem loopPowerGroupShiftNatIsoZero (k : ℕ) :
    loopPowerGroupShiftNatIso.{u, v} 0 k = (PointedCGWH.piNPositiveFunctor k).leftUnitor := rfl

/-- The full component retains both original group maps at every actual original loop power. -/
def loopPowerGroupShiftIsoComponent (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPower n ⋙ PointedCGWH.piNPositiveFunctor k).obj X ≅
      (PointedCGWH.piNPositiveFunctor (k + n)).obj X :=
  (loopPowerGroupShiftNatIso n k).app X

/-- Every entire original pointed map retains the full forward loop-power group naturality. -/
theorem loopPowerGroupShiftNatIso_hom_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor k).map ((loopPower n).map f) ≫
        (loopPowerGroupShiftIsoComponent n k Y).hom =
      (loopPowerGroupShiftIsoComponent n k X).hom ≫
        (PointedCGWH.piNPositiveFunctor (k + n)).map f :=
  (loopPowerGroupShiftNatIso n k).hom.naturality f

/-- Every entire original pointed map retains the full inverse loop-power group naturality. -/
theorem loopPowerGroupShiftNatIso_inv_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (k + n)).map f ≫
        (loopPowerGroupShiftIsoComponent n k Y).inv =
      (loopPowerGroupShiftIsoComponent n k X).inv ≫
        (PointedCGWH.piNPositiveFunctor k).map ((loopPower n).map f) :=
  (loopPowerGroupShiftNatIso n k).inv.naturality f

/-- The exact original evaluated loop iteration has its full original shifted group NatIso. -/
def iterationGroupEvaluationNatIso (n m k : ℕ) :
    iterate.{u, v} n ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙
        PointedCGWH.piNPositiveFunctor k ≅
      PointedCGWH.SequentialSpectrum.evaluation (m + n) ⋙
        PointedCGWH.piNPositiveFunctor (k + n) :=
  Functor.isoWhiskerRight (iterationEvaluationIso n m) (PointedCGWH.piNPositiveFunctor k) ≪≫
    Functor.associator (PointedCGWH.SequentialSpectrum.evaluation (m + n))
        (loopPower n) (PointedCGWH.piNPositiveFunctor k) ≪≫
      Functor.isoWhiskerLeft (PointedCGWH.SequentialSpectrum.evaluation (m + n))
        (loopPowerGroupShiftNatIso n k)

/-- Each original iterate and level retains the complete group comparison in both directions. -/
def iterationGroupEvaluationIsoComponent (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).obj (((iterate n).obj X).level m) ≅
      (PointedCGWH.piNPositiveFunctor (k + n)).obj (X.level (m + n)) :=
  (iterationGroupEvaluationNatIso n m k).app X

/-- All original spectrum maps retain every complete forward evaluated-iteration group map. -/
theorem iterationGroupEvaluationNatIso_hom_naturality (n m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterate n).map f) m) ≫
          (iterationGroupEvaluationIsoComponent n m k Y).hom =
      (iterationGroupEvaluationIsoComponent n m k X).hom ≫
        (PointedCGWH.piNPositiveFunctor (k + n)).map
          (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) :=
  (iterationGroupEvaluationNatIso n m k).hom.naturality f

/-- All original spectrum maps retain every complete inverse evaluated-iteration group map. -/
theorem iterationGroupEvaluationNatIso_inv_naturality (n m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (k + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) ≫
          (iterationGroupEvaluationIsoComponent n m k Y).inv =
      (iterationGroupEvaluationIsoComponent n m k X).inv ≫
        (PointedCGWH.piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iterate n).map f) m) :=
  (iterationGroupEvaluationNatIso n m k).inv.naturality f

/-- Both complete group comparison maps compose to the same original iterate-level identity. -/
theorem iterationGroupEvaluationIso_hom_inv (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationIsoComponent n m k X).hom ≫
        (iterationGroupEvaluationIsoComponent n m k X).inv =
      𝟙 ((PointedCGWH.piNPositiveFunctor k).obj (((iterate n).obj X).level m)) :=
  (iterationGroupEvaluationIsoComponent n m k X).hom_inv_id

/-- Both complete group comparison maps compose to the same original shifted-level identity. -/
theorem iterationGroupEvaluationIso_inv_hom (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationGroupEvaluationIsoComponent n m k X).inv ≫
        (iterationGroupEvaluationIsoComponent n m k X).hom =
      𝟙 ((PointedCGWH.piNPositiveFunctor (k + n)).obj (X.level (m + n))) :=
  (iterationGroupEvaluationIsoComponent n m k X).inv_hom_id

/-- The actual original iterate unit induces the same original adjoint structure group map. -/
theorem iterateUnitGroupMap_eq_adjoint (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) =
      (PointedCGWH.piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap ((iterate n).obj X) m) :=
  congrArg (PointedCGWH.piNPositiveFunctor k).map (iterateUnit_levelMap n X m)

/-- The original group structure map retains the actual original iterate unit and native shift. -/
theorem iterateUnitGroupMap_then_shift (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupStructureNatTrans m k).app ((iterate n).obj X) =
      (PointedCGWH.piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) ≫
        (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) :=
  (congrArg (fun f => (PointedCGWH.piNPositiveFunctor k).map f ≫
    (nativeLoopGroupShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)))
      (iterateUnit_levelMap n X m)).symm

end PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
