/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalLocalization

/-!
# The original native orthogonal stable localization

The actual all-arrow recognition equality and the complete original K
factorization supply left Bousfield localization data for the original
native free/evaluation stabilization maps. Derived locality and local
equivalences use the original native Omega-target Hom tests.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.OriginalFiberNullity

open OperatorStabilizationK
private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev s := Actual.orthogonalFamily.{u, v}
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory SimplicialEnrichment.simplicialCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The localizing arrows are the actual original native free/evaluation maps on every pair. -/
abbrev orthogonalStabilizationArrows := DerivedLocalMapping.stabilizationArrows s

/-- Derived locality uses the complete original native Omega action. -/
theorem orthogonalLocalFibrant_iff_isOmega (X : C.{u, v}) :
    isLocalFibrant orthogonalStabilizationArrows X ↔ NativeK.IsOmega s X :=
  DerivedLocalMapping.isLocalFibrant_iff_isOmega s X

/-- All derived local equivalences are exactly the original Omega Hom tests. -/
theorem orthogonalLocalEquivalences_eq_omegaTests :
    localEquivalences orthogonalStabilizationArrows = NativeK.omegaTests s :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests s

/-- Every original localizing map passes its original derived mapping tests. -/
theorem orthogonalStabilizationArrows_localEquivalence (l : ℕ × ℕ) :
    localEquivalences orthogonalStabilizationArrows (orthogonalStabilizationArrows l).hom :=
  fun _E hE => hE.2 l

/-- The entire localized right class is the original paired K-right class. -/
theorem orthogonalLocalizedFibrations_eq_KRight :
    localizedFibrations orthogonalStabilizationArrows = (NativeK.generators s).rlp := by
  unfold localizedFibrations
  rw [Native.cofibrations_eq, orthogonalLocalEquivalences_eq_omegaTests,
    ← orthogonal_left_class_eq]
  exact (NativeK.generators s).rlp_llp_rlp

/-- Original recognition supplies the complete local trivial-fibration class. -/
theorem orthogonalLocalizedTrivialFibrations_eq_level :
    localizedFibrations orthogonalStabilizationArrows ⊓
        localEquivalences orthogonalStabilizationArrows = trivialFibrations C.{u, v} := by
  rw [orthogonalLocalizedFibrations_eq_KRight, orthogonalLocalEquivalences_eq_omegaTests,
    ← orthogonal_right_class_eq]
  exact Native.Data.generatorsI_rlp

/-- The default terminal arrow and original zero arrow have the same actual K lifting. -/
theorem orthogonalLocalized_terminal_iff_isOmega (X : C.{u, v}) :
    localizedFibrations orthogonalStabilizationArrows (terminal.from X) ↔ NativeK.IsOmega s X := by
  rw [orthogonalLocalizedFibrations_eq_KRight]
  let e := Diagrams.zeroDiagramIsTerminal.uniqueUpToIso (terminalIsTerminal (C := C.{u, v}))
  have h : Diagrams.toZero X ≫ e.hom = terminal.from X :=
    (terminalIsTerminal (C := C.{u, v})).hom_ext _ _
  let d : CategoryTheory.Arrow.mk (Diagrams.toZero X) ≅
      CategoryTheory.Arrow.mk (terminal.from X) :=
    CategoryTheory.Arrow.isoMk (Iso.refl X) e ((Category.id_comp _).trans h.symm)
  exact ((NativeK.generators s).rlp.arrow_mk_iso_iff d).symm.trans
    (NativeK.lifting_toZero_iff_isOmega s X)

/-- The original full factor record proves the localized weak factorization system. -/
theorem orthogonalLocalized_wfs :
    IsWeakFactorizationSystem
      (cofibrations C.{u, v} ⊓ localEquivalences orthogonalStabilizationArrows)
      (localizedFibrations orthogonalStabilizationArrows) := by
  rw [Native.cofibrations_eq, orthogonalLocalEquivalences_eq_omegaTests,
    orthogonalLocalizedFibrations_eq_KRight, ← orthogonal_left_class_eq]
  exact OriginalGeneratedModel.weakFactorizationSystemOfGiven
    (NativeK.generators s) (NativeK.factorizationData s)

/-- Genuine original recognition constructs the full left Bousfield localization packet. -/
theorem orthogonalLeftBousfieldLocalizationData :
    LeftBousfieldLocalizationData orthogonalStabilizationArrows :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalization.data
    (orthogonalComparisonHomBijections (B := B))

/-- The actual canonical stable weak class is the same derived local-equivalence class. -/
theorem orthogonalStableWeak_eq_localEquivalences :
    orthogonalModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      localEquivalences orthogonalStabilizationArrows :=
  orthogonalLocalEquivalences_eq_omegaTests.symm

/-- The actual canonical stable right class is the original localized right class. -/
theorem orthogonalStableFibrations_eq_localized :
    orthogonalModelCategory.{u, v}.categoryWithFibrations.fibrations =
      localizedFibrations orthogonalStabilizationArrows :=
  orthogonalLocalizedFibrations_eq_KRight.symm

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction
