/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceRightModuleActions
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorGeneratorRecovery
public import MathlibExt.Topology.Category.PointedCGWH.Points

/-!
# Entire original native operator recovery from right sphere modules

The recovered generator retains the actual continuous orthogonal Hom,
original representation sphere, original right sphere action, and full
restricted index action. The native unit separator proves the complete
generator identity. Its original mapped coend recovers every entire operator
Hom map. These are carrier reconstruction equations, before the remaining
Day module descent and the full original module-category equivalence.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

open Enriched Enriched.SphereOperator

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory

/-- The original right sphere action and its actual source index block swap. -/
def coefficientFromRightSphere
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (a + n)) :=
  Enriched.SphereOperator.coefficientFromRightSphere
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F n a

/-- The entire derived source coefficient keeps the literal original right action
and restriction. -/
theorem coefficientFromRightSphere_value
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    coefficientFromRightSphere.{u, v} F n a = sphereAction.{u, v} F n a ≫
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
        (β_ a n).inv := rfl

/-- This original right sphere coefficient is exactly the whole original identity-label action. -/
theorem coefficientFromRightSphere_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    coefficientFromRightSphere.{u, v} F n a =
      coefficientAction OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
        F n (a + n) a (𝟙 (a + n)) :=
  Enriched.SphereOperator.coefficientFromRightSphere_original
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F n a

/-- Reconstruct the entire native generator using its original right sphere
and full index action. -/
def recoveredGenerator
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : OrthogonalIndex) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗
      (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a) ⟶
        F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  Enriched.SphereOperator.recoveredGenerator OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F n k a

/-- The whole recovered generator is its original continuous Hom, sphere, and index formula. -/
theorem recoveredGenerator_value
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : OrthogonalIndex) :
    recoveredGenerator.{u, v} F n k a =
      (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ◁
        (β_ (OrthogonalIndex.hom.{u, v} (a + n) k)
          (PointedCGWH.orthogonalSphere.{u, v} a)).hom) ≫
      (α_ (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
        (PointedCGWH.orthogonalSphere.{u, v} a)
        (OrthogonalIndex.hom.{u, v} (a + n) k)).inv ≫
      (coefficientFromRightSphere.{u, v} F n a ▷ OrthogonalIndex.hom.{u, v} (a + n) k) ≫
      MonoidalClosed.uncurry
        (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map (a + n) k) := rfl

/-- Every whole continuous original Hom generator is recovered on all sphere values. -/
theorem generatorAction_eq_recoveredGenerator
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : OrthogonalIndex) :
    generatorAction OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F n k a =
        recoveredGenerator.{u, v} F n k a :=
  Enriched.SphereOperator.generatorAction_eq_recoveredGenerator
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    PointedCGWH.isSeparator_tensorUnit F n k a

/-- All original continuous coefficient-index relations hold for the recovered family. -/
theorem recoveredGenerator_balanced
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k : OrthogonalIndex) :
    weightedCoend.Mapped.Balanced
      (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
      (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
      (recoveredGenerator.{u, v} F n k) :=
  Enriched.SphereOperator.recoveredGenerator_balanced
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    PointedCGWH.isSeparator_tensorUnit F n k

/-- The actual native mapped coend recovers the entire original operator Hom map. -/
theorem full_operator_map_recovery
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k : OrthogonalIndex) :
    MonoidalClosed.curry
      (weightedCoend.Mapped.desc
        (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
        (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
        (recoveredGenerator.{u, v} F n k) (recoveredGenerator_balanced.{u, v} F n k)) =
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  Enriched.SphereOperator.full_operator_map_recovery
    OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    PointedCGWH.isSeparator_tensorUnit F n k

/-- The entire reconstruction function agrees for every actual original operator diagram. -/
theorem full_operator_map_recovery_function :
    (fun (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
        (n k : OrthogonalIndex) =>
      MonoidalClosed.curry
        (weightedCoend.Mapped.desc
          (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
          (tensorLeft (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)))
          (recoveredGenerator.{u, v} F n k) (recoveredGenerator_balanced.{u, v} F n k))) =
      fun (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
          (n k : OrthogonalIndex) =>
        F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k) := by
  funext F n k
  exact full_operator_map_recovery.{u, v} F n k

end CategoryTheory.Spectra.OrthogonalSourceRightModule
