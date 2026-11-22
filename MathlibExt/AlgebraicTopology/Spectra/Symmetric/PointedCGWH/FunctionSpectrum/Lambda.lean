/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Iteration
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Unit
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSource

/-!
# The coaugmentation of the symmetric function-spectrum functor

Precomposition with a unit-index stabilization map, together with the function
spectrum of the unit, gives a natural coaugmentation into the corresponding
free-source function spectrum. Specializing to the one-element index and comparing
its sphere coefficient with the one-sphere defines the first coaugmentation.
Its naturality is recorded both for spectrum maps and for the enriched Hom actions.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricLambda
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- Every original unit-index stabilization keeps its full source coefficient and index. -/
def unitStabilization (r : I) :
    Free.object (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
        (S.{u, v}.functor.obj r) ⟶
      Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricStabilization
    (𝟙_ I) r

/-- The entire actual function target of the original unit-index sphere source. -/
def sourceTarget (r : I) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  NativeOmegaPreparation.NativeSymmetricFunction.functor
    (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
      (S.{u, v}.functor.obj r))

/-- This family keeps the whole original function functor as its literal value. -/
theorem sourceTarget_original (r : I) : sourceTarget.{u, v} r =
    NativeOmegaPreparation.NativeSymmetricFunction.functor
      (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} ((𝟙_ I) ⊗ r))
        (S.{u, v}.functor.obj r)) := rfl

/-- The original source pre-map and genuine native unit give every complete unit-index map. -/
def sourceCoaugmentation (r : I) : 𝟭 Carrier.{u, v} ⟶ sourceTarget.{u, v} r :=
  NativeSymmetricFreeFunction.nativeUnitComparison.inv ≫
    NativeOmegaPreparation.NativeSymmetricFunction.precompose (unitStabilization r)

theorem sourceCoaugmentation_naturality (r : I) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    f ≫ (sourceCoaugmentation r).app Y = (sourceCoaugmentation r).app X ≫
      (sourceTarget r).map f :=
  (sourceCoaugmentation r).naturality f

/-- The first original source stabilization, with its actual cardinal-one object. -/
def firstStabilization :
    Free.object (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
        (S.{u, v}.functor.obj NativeSymmetricDelooping.firstIndex) ⟶
      Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v}) :=
  unitStabilization NativeSymmetricDelooping.firstIndex

/-- The actual first sphere comparison precedes that same original source stabilization. -/
def firstSource :
    Free.object (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
        PointedCGWH.sphereOne.{u, v} ⟶
      Free.object (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v}) :=
  Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
      NativeSymmetricDelooping.firstCoefficientIso.inv ≫ firstStabilization

/-- Actual function precomposition gives the original first-free coaugmentation. -/
def coaugmentation :
    (fun (C₀ : Type _) [Category.{v} C₀] (F : C₀ ⥤ C₀) =>
      @Quiver.Hom (C₀ ⥤ C₀)
        ((Functor.category : Category (C₀ ⥤ C₀)).toCategoryStruct.toQuiver) (𝟭 C₀) F)
      _ NativeSymmetricR.functor.{u, v} :=
  NativeSymmetricFreeFunction.nativeUnitComparison.inv ≫
    NativeOmegaPreparation.NativeSymmetricFunction.precompose firstSource

theorem coaugmentation_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    f ≫ coaugmentation.app Y = coaugmentation.app X ≫ NativeSymmetricR.functor.map f :=
  coaugmentation.naturality f

theorem firstSource_original : firstSource.{u, v} =
    Free.coefficientMap
        (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
        NativeSymmetricDelooping.firstCoefficientIso.inv ≫
      unitStabilization NativeSymmetricDelooping.firstIndex := rfl

theorem coaugmentation_original : coaugmentation.{u, v} =
    NativeSymmetricFreeFunction.nativeUnitComparison.inv ≫
      NativeOmegaPreparation.NativeSymmetricFunction.precompose firstSource := rfl

/-- Every full original operator Hom obeys the actual source coaugmentation square. -/
theorem coaugmentation_fullHom_naturality (X : Carrier.{u, v}) (j k : J.{u, v}) :
    (β_ (𝟙_ V.{u, v}) (j ⟶[V.{u, v}] k)).hom ≫
        (X.toEnrichedFunctor.map j k ⊗ₘ (coaugmentation.app X).app k) ≫
        eComp V.{u, v} (X.toEnrichedFunctor.obj j) (X.toEnrichedFunctor.obj k)
          ((NativeSymmetricR.functor.obj X).toEnrichedFunctor.obj k) =
      ((coaugmentation.app X).app j ⊗ₘ (NativeSymmetricR.functor.obj X).toEnrichedFunctor.map j k) ≫
        eComp V.{u, v} (X.toEnrichedFunctor.obj j)
          ((NativeSymmetricR.functor.obj X).toEnrichedFunctor.obj j)
          ((NativeSymmetricR.functor.obj X).toEnrichedFunctor.obj k) :=
  (coaugmentation.app X).naturality j k

end NativeOmegaRecovery.NativeSymmetricLambda
