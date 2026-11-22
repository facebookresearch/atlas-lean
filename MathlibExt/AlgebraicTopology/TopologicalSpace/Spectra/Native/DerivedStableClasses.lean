/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationKAdapter
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorHomCofibrant
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ThomCofibrant
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK

/-!
# Derived local classes on the three original native spectrum carriers

The native derived mapping criterion identifies the original Omega Hom
tests with derived local equivalences for each whole original stabilization
family. The sequential degree, symmetric paired finite sets and orthogonal
paired dimensions remain unchanged.

The original sphere, orbit-copower and Thom cell proofs discharge index-Hom
cofibrancy. The full original K-left class and every K generator therefore
satisfy the derived local tests on arbitrary endpoints. These results use
the constructed native level model and its actual singular mapping ends.
The native stable model construction remains a separate required join.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeDerivedStable

attribute [local instance]
  HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping.cofibrantFactorization
  HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping.fibrantFactorization

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole original sequential family gives precisely the original native Omega tests. -/
theorem sequential_localEquivalences_eq_omegaTests :
    localEquivalences (DerivedLocalMapping.stabilizationArrows
      SequentialSpectrum.StabilizationKAdapter.family.{u, v}) =
      NativeK.omegaTests SequentialSpectrum.StabilizationKAdapter.family :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests
    SequentialSpectrum.StabilizationKAdapter.family

/-- Every original paired symmetric label is retained by the native derived-local class. -/
theorem symmetric_localEquivalences_eq_omegaTests :
    localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.symmetricFamily.{u, v}) =
      NativeK.omegaTests Actual.symmetricFamily :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests Actual.symmetricFamily

/-- Every original paired orthogonal label is retained by the native derived-local class. -/
theorem orthogonal_localEquivalences_eq_omegaTests :
    localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.orthogonalFamily.{u, v}) =
      NativeK.omegaTests Actual.orthogonalFamily :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests Actual.orthogonalFamily

/-- The original sequential sphere Hom proof makes all K-left arrows derived locally weak. -/
theorem sequentialKLeft_le_localEquivalences :
    (NativeK.generators SequentialSpectrum.StabilizationKAdapter.family.{u, v}).rlp.llp ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows
        SequentialSpectrum.StabilizationKAdapter.family) :=
  DerivedLocalMapping.KLeft_le_localEquivalences SequentialSpectrum.StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant

/-- The actual orbit-copower Hom proof gives the whole original symmetric K-left class. -/
theorem symmetricKLeft_le_localEquivalences :
    (NativeK.generators Actual.symmetricFamily.{u, v}).rlp.llp ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.symmetricFamily) :=
  DerivedLocalMapping.KLeft_le_localEquivalences Actual.symmetricFamily
    PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant

/-- The original Thom cell proof gives the whole original orthogonal K-left class. -/
theorem orthogonalKLeft_le_localEquivalences :
    (NativeK.generators Actual.orthogonalFamily.{u, v}).rlp.llp ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.orthogonalFamily) := by
  apply DerivedLocalMapping.KLeft_le_localEquivalences Actual.orthogonalFamily
  rintro ⟨a⟩ ⟨b⟩
  exact CategoryTheory.Spectra.OrthogonalCoendThom.nativeHom_isCofibrant a b

/-- Every original sequential K horn and sphere-boundary generator is derived locally weak. -/
theorem sequentialKGenerators_le_localEquivalences :
    NativeK.generators SequentialSpectrum.StabilizationKAdapter.family.{u, v} ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows
        SequentialSpectrum.StabilizationKAdapter.family) :=
  (NativeK.generators SequentialSpectrum.StabilizationKAdapter.family).le_llp_rlp.trans
    sequentialKLeft_le_localEquivalences

/-- The unchanged full symmetric K union retains every horn, pair and boundary dimension. -/
theorem symmetricKGenerators_le_localEquivalences :
    NativeK.generators Actual.symmetricFamily.{u, v} ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.symmetricFamily) :=
  (NativeK.generators Actual.symmetricFamily).le_llp_rlp.trans symmetricKLeft_le_localEquivalences

/-- The unchanged full orthogonal K union retains every horn, pair and boundary dimension. -/
theorem orthogonalKGenerators_le_localEquivalences :
    NativeK.generators Actual.orthogonalFamily.{u, v} ≤
      localEquivalences (DerivedLocalMapping.stabilizationArrows Actual.orthogonalFamily) :=
  (NativeK.generators Actual.orthogonalFamily).le_llp_rlp.trans orthogonalKLeft_le_localEquivalences

/-- Every original sequential arrow has the complete chosen derived Omega-target criterion. -/
theorem sequential_omegaTests_iff_derivedPrecomp_weak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests SequentialSpectrum.StabilizationKAdapter.family f ↔
      ∀ E : PointedCGWH.SequentialSpectrum.{u, v},
        NativeK.IsOmega SequentialSpectrum.StabilizationKAdapter.family E →
          SSet.realizationWeakEquivalences (derivedMappingPrecomp f E) :=
  DerivedLocalMapping.omegaTests_iff_derivedPrecomp_weak
    SequentialSpectrum.StabilizationKAdapter.family f

/-- Every original symmetric arrow has all full native Omega-target mapping tests. -/
theorem symmetric_omegaTests_iff_derivedPrecomp_weak
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests Actual.symmetricFamily f ↔
      ∀ E : Actual.SymmetricCarrier.{u, v}, Actual.SymmetricIsOmega E →
        SSet.realizationWeakEquivalences (derivedMappingPrecomp f E) :=
  DerivedLocalMapping.omegaTests_iff_derivedPrecomp_weak Actual.symmetricFamily f

/-- Every original orthogonal arrow has all full native Omega-target mapping tests. -/
theorem orthogonal_omegaTests_iff_derivedPrecomp_weak
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests Actual.orthogonalFamily f ↔
      ∀ E : Actual.OrthogonalCarrier.{u, v}, Actual.OrthogonalIsOmega E →
        SSet.realizationWeakEquivalences (derivedMappingPrecomp f E) :=
  DerivedLocalMapping.omegaTests_iff_derivedPrecomp_weak Actual.orthogonalFamily f

end PointedCGWH.Spectra.NativeDerivedStable
