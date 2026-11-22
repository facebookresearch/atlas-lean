/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.NativeScalarLeftComparison
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# The native symmetric tensor bifunctor

Identifies the tensor bifunctor of native symmetric spectra with the relative tensor transported through the sphere-module equivalence, and hence with the specified native smash bifunctor.
-/

set_option autoImplicit false
noncomputable section
universe u v uP vP uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

private theorem eqToIso_app {P : Type uP} [Category.{vP} P]
    {D : Type uD} [Category.{vD} D] {F G : P ⥤ D} (h : F = G) (X : P) :
    (eqToIso h).app X = eqToIso (Functor.congr_obj h X) := by
  cases h
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

set_option maxHeartbeats 500000 in
-- The native tensor is the relative tensor transported through the module equivalence.
private theorem nativeTensorBifunctor_eq_original :
    MonoidalCategory.curriedTensor Carrier.{u, v} =
      Mod.EquivalenceFunctionTransport.smashBifunctor A.{u, v} E.{u, v} := rfl

/-- The complete transported tensor bifunctor retains the entire original native balanced-smash source. -/
theorem nativeTensorBifunctor_eq_boundary :
    MonoidalCategory.curriedTensor Carrier.{u, v} = nativeSmashBifunctorBoundary.{u, v} :=
  nativeTensorBifunctor_eq_original.trans nativeSmashBifunctorBoundary_whole.symm




end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
