/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientAdjunct

/-!
# Every original first-source coefficient retains its native Day module arrow

The original first coefficient isomorphism is inverted before the unit-index
stabilization. The complete native source arrow is retained for every map
into the original one-sphere; no point is selected.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.OriginalNativeFirstSourceDayMapComposition

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

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

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeSource
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK


/-- Every original scalar map into the one-sphere retains the complete actual
lambda source. The original first coefficient inverse precedes stabilization. -/
theorem actualFirstSource_preCoefficient {W : V.{u, v}}
    (g : W ⟶ PointedCGWH.sphereOne.{u, v}) :
    (Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map g ≫
        sourceArrow.{u, v} (r := 𝟙_ I) (s := NativeSymmetricDelooping.firstIndex)
          (M := 𝟙_ V.{u, v}) (M' := PointedCGWH.sphereOne.{u, v})
          NativeSymmetricLambda.firstSource.{u, v} =
      (Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map
          (g ≫ NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv) ≫
        moduleStabilization.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex := by
  have hSource := NativeSymmetricSourceComposite.actualFirstSource_moduleArrow.{u, v}
  have h := congrArg
    (fun p => (Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map g ≫ p)
    hSource
  exact h.trans ((Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map_comp_assoc
    g NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv
    (moduleStabilization.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex)).symm

/-- The SAME complete native Day adjunction transposes the original first
source after every coefficient map, preserving both chosen source comparisons. -/
theorem actualFirstSource_preCoefficient_adjunct {W : V.{u, v}}
    (g : W ⟶ PointedCGWH.sphereOne.{u, v}) :
    type_of% (congrArg
      ((Mod.dayFreeAtEvaluationAdjunction S.{u, v} NativeSymmetricDelooping.firstIndex).homEquiv
        W (freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})))
      (actualFirstSource_preCoefficient.{u, v} g)) :=
  congrArg
    ((Mod.dayFreeAtEvaluationAdjunction S.{u, v} NativeSymmetricDelooping.firstIndex).homEquiv
      W (freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})))
    (actualFirstSource_preCoefficient.{u, v} g)

end NativeOmegaRecovery.OriginalNativeFirstSourceDayMapComposition
