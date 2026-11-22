/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.KOmegaRecognition
import MathlibExt.AlgebraicTopology.Spectra.Sequential.KLocalReplacement
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKReflection
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKAllSourceLocality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel

/-!
# Original sequential localization entry points from the canonical native family

The same original family and original K unit specialize the complete
native all-source Hom results. Actual sphere-coordinate Hom cofibrancy is
proved by the public level constructor. No source-fiber-sequence result
or supplied reflector is used to obtain these original entry points.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.SequentialSpectrum.StableK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Both original Omega predicates refer to the same original K zero-arrow tests. -/
theorem nativeOmega_iff_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    NativeK.IsOmega StabilizationKAdapter.family X ↔ X.IsOmega := by
  calc
    NativeK.IsOmega StabilizationKAdapter.family X ↔
        (NativeK.generators StabilizationKAdapter.family).rlp (toZero X) :=
      (NativeK.lifting_toZero_iff_isOmega StabilizationKAdapter.family X).symm
    _ ↔ generators.rlp (toZero X) := by rw [StabilizationKAdapter.generators_eq]
    _ ↔ X.IsOmega := lifting_toZero_iff_isOmega X

/-- The whole original bare K detected class uses the same actual native replacement map. -/
abbrev originalKDetectedWeakEquivalences :
    MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.originalKDetectedWeakEquivalences StabilizationKAdapter.family

/-- Original source arrows keep the exact native bare K versus local-test comparison. -/
theorem originalKReplacementMap_weak_iff_localTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (localReplacement.map f) ↔
      localTestEquivalences f :=
  NativeK.originalKReplacementMap_weak_iff_localTests StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant f

/-- Equality keeps every original source arrow and the complete actual native K map. -/
theorem originalKDetectedWeak_eq_localTests :
    originalKDetectedWeakEquivalences.{u, v} = localTestEquivalences :=
  NativeK.originalKDetectedWeak_eq_localTests StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant

/-- The original all-source unit has the same complete canonical native local tests. -/
theorem originalKUnit_localTestEquivalence_allSource (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localTestEquivalences (localReplacementUnit.app X) :=
  NativeK.originalKUnit_localTestEquivalence_allSource StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant X

/-- The original categorical local-test projection is the same canonical-family construction. -/
abbrev localTestLocalization := NativeK.localTestLocalization.{u, v} StabilizationKAdapter.family

/-- The original entry point localizes the full actual canonical native local-test class. -/
theorem localTestLocalization_isLocalization :
    localTestLocalization.{u, v}.IsLocalization localTestEquivalences :=
  NativeK.localTestLocalization_isLocalization StabilizationKAdapter.family

/-- Both original unit Hom functions are the actual complete native functions on every source. -/
def originalKUnitHomEquiv (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) :
    ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj (localReplacement.obj X) ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) ≃
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :=
  NativeK.originalKUnitHomEquiv StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant X Z
    (by simpa only [StabilizationKAdapter.generators_eq] using hZ)

/-- The full native Hom input is precomposed with the same original K injection. -/
theorem originalKUnitHomEquiv_apply (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z))
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj (localReplacement.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    originalKUnitHomEquiv X Z hZ g =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
        (localReplacementUnit.app X) ≫ g :=
  NativeK.originalKUnitHomEquiv_apply StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant X Z
    (by simpa only [StabilizationKAdapter.generators_eq] using hZ) g

/-- Equality retains both whole native functions and their original source and target carriers. -/
theorem originalKUnitHomEquiv_eq_native (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) :
    originalKUnitHomEquiv X Z hZ =
      NativeK.originalKUnitHomEquiv StabilizationKAdapter.family
        PointedCGWH.Spectra.Sequential.hom_isCofibrant X Z
        (by simpa only [StabilizationKAdapter.generators_eq] using hZ) := rfl

end PointedCGWH.SequentialSpectrum.StableK

namespace PointedCGWH.NativeOrderedMappingTelescope.NativeKLocalLiftingGeometry

open PointedCGWH.SequentialSpectrum.StableK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The complete original local Hom tests keep precisely the original ordinary Omega targets. -/
theorem originalLocalTestEquivalence_iff_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    localTestEquivalences f ↔
      ∀ Z : PointedCGWH.SequentialSpectrum.{u, v}, Z.IsOmega → Function.Bijective
        (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
            (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
          (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) := by
  rw [localTestEquivalences_iff_liftingTests]
  exact ⟨fun h Z hZ => h Z ((lifting_toZero_iff_isOmega Z).mpr hZ),
    fun h Z hZ => h Z ((lifting_toZero_iff_isOmega Z).mp hZ)⟩

end PointedCGWH.NativeOrderedMappingTelescope.NativeKLocalLiftingGeometry

namespace PointedCGWH.NativeOrderedMappingTelescope.NativeKStableAcyclicityGeometry

open PointedCGWH.SequentialSpectrum PointedCGWH.SequentialSpectrum.StableK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual original K-left map has all native local tests on arbitrary original endpoints. -/
theorem originalKLeft_localTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : generators.rlp.llp f) : localTestEquivalences f :=
  NativeK.originalKLeft_localTests StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant f
    (by simpa only [StabilizationKAdapter.generators_eq] using hf)

end PointedCGWH.NativeOrderedMappingTelescope.NativeKStableAcyclicityGeometry
