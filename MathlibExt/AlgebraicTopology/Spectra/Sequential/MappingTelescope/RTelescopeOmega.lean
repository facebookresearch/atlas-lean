/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopWeakDetection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.AllDegreeTypeStructure

/-!
# The SAME actual original R of the telescope and its positive stages are Omega

The original ALL-degree telescope adjoint piN maps and genuine ALL-point
native-loop detector prove that the SAME original R(telescope X) is Omega
for EVERY input. Every positive original R iterate is Omega as well. The
actual original R-unit and all positive original MC transitions on this
input are weak in the SAME caller-B native level model. Their whole map
families, every original input Arrow and every level are retained. The
original telescope itself still needs finite-stage all-point transport;
this result makes no replacement of that telescope or its original R,
MC/model/cardinality/source choices and assumes no desired Omega law.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.RTelescopeOmegaGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopWeakDetectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.AllDegreeTypeStructureGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The WHOLE original R-telescope adjoint family retains the actual original looped adjoints. -/
theorem rTelescope_adjoint_components (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (fun m => PointedCGWH.SequentialSpectrum.adjointStructureMap (functor.obj (telescope X)) m) =
      (fun m => PointedCGWH.loop.map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) (m + 1))) := by
  funext m
  exact functor_adjointStructureMap (telescope X) m

/-- The ENTIRE original R-unit family on R of the telescope keeps every original input map. -/
def rTelescopeUnitNatTrans : telescopeFunctor.{u, v} ⋙ functor ⟶
    (telescopeFunctor ⋙ functor) ⋙ functor :=
  (telescopeFunctor ⋙ functor).rightUnitor.inv ≫
    Functor.whiskerLeft (telescopeFunctor ⋙ functor) PointedCGWH.SequentialSpectrum.OrderedLoop.unit

/-- EVERY entire original unit component is the SAME actual R-unit at R(telescope X). -/
theorem rTelescopeUnitNatTrans_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    rTelescopeUnitNatTrans.app X =
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (functor.obj (telescope X)) := by
  change 𝟙 _ ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app _ = _
  exact Category.id_comp _

/-- EVERY original unit level is the actual original R-telescope adjoint map. -/
theorem rTelescopeUnitNatTrans_levelMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (rTelescopeUnitNatTrans.app X) m =
      PointedCGWH.SequentialSpectrum.adjointStructureMap (functor.obj (telescope X)) m :=
  (congrArg (fun f => PointedCGWH.SequentialSpectrum.levelMap f m)
    (rTelescopeUnitNatTrans_app X)).trans (unit_levelMap (functor.obj (telescope X)) m)

/-- The WHOLE actual original unit component family is the SAME original looped adjoint family. -/
theorem rTelescopeUnitNatTrans_loop_components (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (fun m => PointedCGWH.SequentialSpectrum.levelMap (rTelescopeUnitNatTrans.app X) m) =
      (fun m => PointedCGWH.loop.map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) (m + 1))) := by
  funext m
  exact (rTelescopeUnitNatTrans_levelMap X m).trans
    (functor_adjointStructureMap (telescope X) m)

/-- EVERY whole input-spectrum Arrow preserves the complete original R-telescope unit square. -/
theorem rTelescopeUnitNatTrans_naturality
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    functor.map (telescopeFunctor.map f) ≫ rTelescopeUnitNatTrans.app Y =
      rTelescopeUnitNatTrans.app X ≫ functor.map (functor.map (telescopeFunctor.map f)) :=
  rTelescopeUnitNatTrans.naturality f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- EVERY actual original telescope adjoint loop map is weak at ALL source loop points. -/
theorem loopTelescopeAdjoint_weak (m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.loop.map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m)).right :=
  PointedCGWH.LoopGeometry.loopMap_weak_of_basedPositive _
    (fun n => telescopeAdjointPiNMap_bijective m (n + 1) X)

/-- The SAME original R(telescope X) is genuinely underlying Omega for EVERY original input. -/
theorem rTelescope_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (functor.obj (telescope X)).IsOmega := by
  intro m
  change CGWH.weakHomotopyEquivalences
    (PointedCGWH.SequentialSpectrum.adjointStructureMap (functor.obj (telescope X)) m).right
  have h := functor_adjointStructureMap (telescope X) m
  exact (congrArg (fun f : (functor.obj (telescope X)).level m ⟶
      PointedCGWH.loop.obj ((functor.obj (telescope X)).level (m + 1)) =>
        CGWH.weakHomotopyEquivalences f.right) h).mpr (loopTelescopeAdjoint_weak (m + 1) X)

/-- EVERY positive SAME original R iterate of the actual telescope is Omega. -/
theorem positiveIterationTelescope_isOmega (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ((iterate (n + 1)).obj (telescope X)).IsOmega := by
  induction n with
  | zero => exact rTelescope_isOmega X
  | succ n hn => exact functor_isOmega _ hn

/-- The ENTIRE SAME original R-unit on R(telescope X) is weak in the original caller-B model. -/
theorem rTelescopeUnit_levelWeak (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (rTelescopeUnitNatTrans.app X) :=
  (rTelescopeUnitNatTrans_app X).symm ▸
    (unit_levelWeak_iff _).mpr (rTelescope_isOmega X)

/-- EVERY actual original R-unit component is weak in the SAME underlying CGWH class. -/
theorem rTelescopeUnit_component_weak (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.levelMap (rTelescopeUnitNatTrans.app X) m).right := by
  have h := rTelescopeUnitNatTrans_levelMap X m
  exact (congrArg (fun f : (functor.obj (telescope X)).level m ⟶
      PointedCGWH.loop.obj ((functor.obj (telescope X)).level (m + 1)) =>
        CGWH.weakHomotopyEquivalences f.right) h).mpr (rTelescope_isOmega X m)

/-- EVERY positive original iterate unit is level weak on the SAME actual original telescope. -/
theorem positiveIterationUnit_levelWeak (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      ((iterateUnit (n + 1)).app (telescope X)) :=
  (iterateUnit_app (n + 1) (telescope X)).symm ▸
    (unit_levelWeak_iff _).mpr (positiveIterationTelescope_isOmega n X)

/-- EVERY actual positive original iterate-unit level is weak in the SAME underlying class. -/
theorem positiveIterationUnit_component_weak (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.levelMap
        ((iterateUnit (n + 1)).app (telescope X)) m).right := by
  have h := iterateUnit_levelMap (n + 1) (telescope X) m
  exact (congrArg (fun f : ((iterate (n + 1)).obj (telescope X)).level m ⟶
      PointedCGWH.loop.obj (((iterate (n + 1)).obj (telescope X)).level (m + 1)) =>
        CGWH.weakHomotopyEquivalences f.right) h).mpr
          (positiveIterationTelescope_isOmega n X m)

/-- EVERY positive ORIGINAL MC transition on the actual telescope is weak in the SAME model. -/
theorem positiveMCTransition_levelWeak (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      ((transition (n + 1)).app (telescope X)) :=
  by
    let W := weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
    have hp : W ((projection (n + 1)).app (telescope X)) :=
      (HomotopicalAlgebra.weakEquivalence_iff _).mp
        (projection_weakEquivalence (n + 1) (telescope X))
    have ht : W ((projection (n + 2)).app (telescope X)) :=
      (HomotopicalAlgebra.weakEquivalence_iff _).mp
        (projection_weakEquivalence (n + 2) (telescope X))
    have hu : W ((iterateUnit (n + 1)).app (telescope X)) := positiveIterationUnit_levelWeak n X
    have h := congr_app (transition_projection (n + 1)) (telescope X)
    have hw : W ((transition (n + 1)).app (telescope X) ≫
        (projection (n + 2)).app (telescope X)) :=
      (congrArg (fun f : (stage (n + 1)).functor.obj (telescope X) ⟶
        (iterate (n + 2)).obj (telescope X) => W f) h).mpr (W.comp_mem _ _ hp hu)
    exact W.of_postcomp _ _ ht hw

/-- EVERY actual positive original MC transition level is weak at ALL underlying source points. -/
theorem positiveMCTransition_component_weak (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.levelMap
        ((transition (n + 1)).app (telescope X)) m).right := by
  let f := (transition (n + 1)).app (telescope X)
  have h : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f :=
    positiveMCTransition_levelWeak n X
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at h
  have he := (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} =>
      CategoryTheory.EnrichedFunctorCat.evaluation a)
    (weakEquivalences PointedCGWH.{u, v}) f).mp h
  have hp : WeakEquivalence (PointedCGWH.SequentialSpectrum.levelMap f m) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (he (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m))
  exact ((PointedCGWH.weakEquivalence_iff _).mp hp).mem

end PointedCGWH.SequentialSpectrum.MappingTelescope.RTelescopeOmegaGeometry
