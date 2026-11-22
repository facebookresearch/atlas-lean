/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeSymmetricOriginalSourceGEN
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaCoordinateReadback

/-!
# Original signed integer isomorphisms imply every native symmetric Omega test

The complete original GEN equality supplies the source equation for every
original input and native degree. The existing original permutation-corrected
lambda/telescope and all-Omega-target Hom retraction prove the forward detector
for every original arrow and every original signed integer functor.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests

open CategoryTheory MonoidalCategory HomotopicalAlgebra CategoryTheory.Spectra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open NativeOmegaRecovery
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open NativeOmegaRecovery.NativeSymmetricSourceGEN.WholeOriginalGEN
open scoped MonoidalClosed CGWH.modelCategory

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- The whole first source comparison is evaluated only after its full
native GEN equality. Every original input and degree retain the original
coefficient inverse and native right-degree transpose. -/
theorem original_sourceEquation (X : Carrier.{u, v}) (m : ℕ) :
    (originalCoordinate.{u, v} m).app X =
      NativeSymmetricDelooping.omegaMap X (finiteIndex m) (finiteIndex 1) ≫
        (firstScalarIso ((bare X).obj (finiteIndex (m + 1)))).hom := by
  have hWord : NativeSymmetricLambda.coaugmentation.{u, v} ≫
      NativeSymmetricR.comparison.{u, v}.hom = originalFirstComparison.{u, v} := rfl
  have hWhole := hWord.trans original_firstSource_whole_gen.{u, v}
  have hEvaluated := congrArg
    (fun z : 𝟭 Carrier.{u, v} ⟶ (PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex ⋙
        cotensor PointedCGWH.sphereOne.{u, v}) =>
      (level.{u, v} m).map (z.app X)) hWhole
  have hCoordinate := originalCoordinate_first_free_comparison.{u, v} m X
  have hStructure : (level.{u, v} m).map (originalFirstStructure.{u, v}.app X) =
      NativeSymmetricDelooping.omegaMap X (finiteIndex m) (finiteIndex 1) ≫
        (firstScalarIso ((bare X).obj (finiteIndex (m + 1)))).hom :=
    originalFirstStructure_component X (finiteIndex m)
  exact hCoordinate.trans (hEvaluated.trans hStructure)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every genuine signed integer isomorphism gives bijective linear
precomposition into every original Omega target in the native level homotopy category. -/
theorem originalPrecomp_bijective {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f))
    (E : Carrier.{u, v}) (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    Function.Bijective (fun g : (toHomotopyCategory Carrier.{u, v}).obj Y ⟶
      (toHomotopyCategory Carrier.{u, v}).obj E =>
        (toHomotopyCategory Carrier.{u, v}).map f ≫ g) :=
  originalPrecomp_bijective_of_sourceEquation original_sourceEquation.{u, v} f hPi E hE

/-- The original source word proves the forward signed-integer criterion
for all original native arrows, with their exact original Omega-target tests. -/
theorem integerIsos_imply_omegaTests {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    NativeK.omegaTests Actual.symmetricFamily f :=
  integerIsos_imply_omegaTests_of_sourceEquation original_sourceEquation.{u, v} f hPi





end PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests
