/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableFactorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses

/-!
# Actual native spectrum factorizations in the stable candidate classes

All six records are constructed from the original native I and K
small-object records at the original realized cardinal and caller bottom.
The three native index-Hom cofibrancy proofs discharge the K-left
classification hypotheses. No factorization, stable model or stable
weak-equivalence outcome is an input.

The records are on the unchanged original sequential, symmetric and
orthogonal enriched spectrum categories. Their full middle functors,
factor maps, Arrow naturalities and factor equations are inherited from
the same original records through membership reclassification only.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.NativeStable

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original sequential I algorithm is classified in the full stable candidate classes. -/
def sequentialIFactorizationData :
    FunctorialFactorizationData
      (NativeK.levelI (I := PointedCGWH.Spectra.Sequential.Index.{u, v})).rlp.llp
      ((NativeK.generators SequentialSpectrum.StabilizationKAdapter.family).rlp ⊓
        NativeK.omegaTests SequentialSpectrum.StabilizationKAdapter.family) :=
  StableFactorization.cofibrantFactorizationData SequentialSpectrum.StabilizationKAdapter.family

/-- The original sequential K algorithm uses its proved original sphere-coordinate cells. -/
def sequentialKFactorizationData :
    FunctorialFactorizationData
      ((NativeK.levelI (I := PointedCGWH.Spectra.Sequential.Index.{u, v})).rlp.llp ⊓
        NativeK.omegaTests SequentialSpectrum.StabilizationKAdapter.family)
      (NativeK.generators SequentialSpectrum.StabilizationKAdapter.family).rlp :=
  StableFactorization.fibrantFactorizationData SequentialSpectrum.StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant

/-- The original symmetric I algorithm retains all finite-bijection and base-arrow labels. -/
def symmetricIFactorizationData :
    FunctorialFactorizationData
      (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp.llp
      ((NativeK.generators Actual.symmetricFamily).rlp ⊓
        NativeK.omegaTests Actual.symmetricFamily) :=
  StableFactorization.cofibrantFactorizationData Actual.symmetricFamily

/-- The full paired symmetric K algorithm uses actual orbit-copower Hom cofibrancy. -/
def symmetricKFactorizationData :
    FunctorialFactorizationData
      ((NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp.llp ⊓
        NativeK.omegaTests Actual.symmetricFamily)
      (NativeK.generators Actual.symmetricFamily).rlp :=
  StableFactorization.fibrantFactorizationData Actual.symmetricFamily
    PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant

/-- The original orthogonal I algorithm retains every continuous operator-index object. -/
def orthogonalIFactorizationData :
    FunctorialFactorizationData
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp.llp
      ((NativeK.generators Actual.orthogonalFamily).rlp ⊓
        NativeK.omegaTests Actual.orthogonalFamily) :=
  StableFactorization.cofibrantFactorizationData Actual.orthogonalFamily

/-- The full paired orthogonal K algorithm uses the proved original Thom cell construction. -/
def orthogonalKFactorizationData :
    FunctorialFactorizationData
      ((NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp.llp ⊓
        NativeK.omegaTests Actual.orthogonalFamily)
      (NativeK.generators Actual.orthogonalFamily).rlp :=
  StableFactorization.fibrantFactorizationData Actual.orthogonalFamily orthogonalHom_isCofibrant

end PointedCGWH.Spectra.NativeStable
