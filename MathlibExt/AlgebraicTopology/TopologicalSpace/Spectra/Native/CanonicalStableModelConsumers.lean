/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableModels
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic

/-!
# Concrete consumers of the original native stable models

The sequential localization is constructed from the already proved native
I/K recognition and the actual original factor records. Its entire
stabilization Arrow family, derived local weak class and local fibrant
objects agree with those of the native sequential stable model.

The model value has the original enriched sequential spectrum carrier.
Neither a model nor a localization record is a caller hypothesis.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableModelConsumers

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev SI := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev SC := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev sSeq := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The complete original native sequential stabilization family is retained literally. -/
abbrev sequentialStabilizationArrows : ℕ → Arrow SC.{u, v} :=
  DerivedLocalMapping.stabilizationArrows sSeq

/-- Every full native derived local test is the original Omega-target Hom test. -/
theorem sequentialLocalEquivalences_eq :
    localEquivalences sequentialStabilizationArrows.{u, v} = NativeK.omegaTests sSeq :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests sSeq

/-- The actual native left recognition law identifies the complete local trivial-left class. -/
theorem sequentialLocalTrivialCofibrations_eq :
    cofibrations SC.{u, v} ⊓ localEquivalences sequentialStabilizationArrows =
      (NativeK.generators sSeq).rlp.llp := by
  rw [sequentialLocalEquivalences_eq,
    HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq]
  exact StableModelConstruction.sequential_left_class_eq.symm

/-- The full localized right class is precisely the original native K-right class. -/
theorem sequentialLocalizedFibrations_eq :
    localizedFibrations sequentialStabilizationArrows.{u, v} =
      (NativeK.generators sSeq).rlp := by
  change (cofibrations SC ⊓ localEquivalences sequentialStabilizationArrows).rlp = _
  rw [sequentialLocalTrivialCofibrations_eq]
  exact (NativeK.generators sSeq).rlp_llp_rlp

/-- The unchanged actual K record supplies the localized weak factorization system. -/
theorem sequentialLocalized_wfs :
    IsWeakFactorizationSystem
      (cofibrations SC.{u, v} ⊓ localEquivalences sequentialStabilizationArrows)
      (localizedFibrations sequentialStabilizationArrows) := by
  rw [sequentialLocalTrivialCofibrations_eq, sequentialLocalizedFibrations_eq]
  exact OriginalGeneratedModel.weakFactorizationSystemOfGiven
    (NativeK.generators sSeq) (NativeK.factorizationData sSeq)

/-- All original endpoints have exactly the original level trivial-right property. -/
theorem sequentialLocalizedTrivialFibrations_eq :
    localizedFibrations sequentialStabilizationArrows.{u, v} ⊓
        localEquivalences sequentialStabilizationArrows = trivialFibrations SC := by
  rw [sequentialLocalizedFibrations_eq, sequentialLocalEquivalences_eq,
    ← StableModelConstruction.sequential_right_class_eq]
  exact HomotopicalAlgebra.EnrichedProjective.Native.Data.generatorsI_rlp

/-- The original K terminal criterion retains the actual zero-terminal comparison. -/
theorem sequentialKRight_terminal_iff_isOmega (X : SC.{u, v}) :
    (NativeK.generators sSeq).rlp (terminal.from X) ↔ NativeK.IsOmega sSeq X := by
  let e : ⊤_ SC.{u, v} ≅ Diagrams.zeroDiagram (A := SI.{u, v}) :=
    terminalIsTerminal.uniqueUpToIso (Diagrams.zeroDiagramIsTerminal (A := SI.{u, v}))
  let a : CategoryTheory.Arrow.mk (terminal.from X) ≅
      CategoryTheory.Arrow.mk (Diagrams.toZero X) :=
    CategoryTheory.Arrow.isoMk' _ _ (Iso.refl X) e
      (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)
  exact ((NativeK.generators sSeq).rlp.arrow_mk_iso_iff a).trans
    (NativeK.lifting_toZero_iff_isOmega sSeq X)

/-- Local fibrant objects are the original complete native sequential Omega objects. -/
theorem sequentialLocalizedFibrations_terminal_iff_isOmega (X : SC.{u, v}) :
    localizedFibrations sequentialStabilizationArrows (terminal.from X) ↔
      NativeK.IsOmega sSeq X := by
  rw [sequentialLocalizedFibrations_eq]
  exact sequentialKRight_terminal_iff_isOmega X

/-- Local Whitehead is the already proved original all-target Omega Hom statement. -/
theorem sequentialLocalEquivalence_iff_levelWeak_of_local
    {X Y : SC.{u, v}} (f : X ⟶ Y)
    (hX : isLocalFibrant sequentialStabilizationArrows X)
    (hY : isLocalFibrant sequentialStabilizationArrows Y) :
    localEquivalences sequentialStabilizationArrows f ↔ weakEquivalences SC f := by
  rw [sequentialLocalEquivalences_eq]
  exact NativeK.omegaTests_iff_levelWeak_of_isOmega sSeq f
    ((DerivedLocalMapping.isLocalFibrant_iff_isOmega sSeq X).mp hX)
    ((DerivedLocalMapping.isLocalFibrant_iff_isOmega sSeq Y).mp hY)

/-- The full sequential localization record follows from the actual original
I/K factors and source recognition; no desired model or localization is supplied. -/
theorem sequentialLeftBousfieldLocalizationData :
    LeftBousfieldLocalizationData sequentialStabilizationArrows.{u, v} where
  localizingMaps l Z hZ := hZ.2 l
  baseWeak_le := by
    rw [sequentialLocalEquivalences_eq]
    exact NativeK.levelWeak_le_omegaTests sSeq
  two_out_of_three := by
    rw [sequentialLocalEquivalences_eq]
    infer_instance
  retracts := by
    rw [sequentialLocalEquivalences_eq]
    infer_instance
  localized_wfs := sequentialLocalized_wfs
  trivialFibrations_eq := sequentialLocalizedTrivialFibrations_eq
  fibrant_iff X :=
    (sequentialLocalizedFibrations_terminal_iff_isOmega X).trans
      (DerivedLocalMapping.isLocalFibrant_iff_isOmega sSeq X).symm
  weakEquivalence_iff_of_local := sequentialLocalEquivalence_iff_levelWeak_of_local

/-- The local weak class belongs to the actual source-constructed native model value. -/
theorem sequentialModelCategory_weakEquivalences_eq_local :
    NativeStableModels.sequentialModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      localEquivalences sequentialStabilizationArrows := by
  change NativeK.omegaTests sSeq = localEquivalences sequentialStabilizationArrows
  exact sequentialLocalEquivalences_eq.symm

/-- The same native model has the actual localized right lifting class. -/
theorem sequentialModelCategory_fibrations_eq_local :
    NativeStableModels.sequentialModelCategory.{u, v}.categoryWithFibrations.fibrations =
      localizedFibrations sequentialStabilizationArrows := by
  change (NativeK.generators sSeq).rlp = localizedFibrations sequentialStabilizationArrows
  exact sequentialLocalizedFibrations_eq.symm

end PointedCGWH.Spectra.NativeStableModelConsumers
