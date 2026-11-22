/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic

/-!
# The original native symmetric stable localization

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

open OperatorStabilizationK
private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev s := Actual.symmetricFamily.{u, v}
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory SimplicialEnrichment.simplicialCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The localizing arrows are the actual original native free/evaluation maps on every pair. -/
abbrev symmetricStabilizationArrows := DerivedLocalMapping.stabilizationArrows s

/-- Derived locality uses the complete original native Omega action. -/
theorem symmetricLocalFibrant_iff_isOmega (X : C.{u, v}) :
    isLocalFibrant symmetricStabilizationArrows X ↔ NativeK.IsOmega s X :=
  DerivedLocalMapping.isLocalFibrant_iff_isOmega s X

/-- All derived local equivalences are exactly the original Omega Hom tests. -/
theorem symmetricLocalEquivalences_eq_omegaTests :
    localEquivalences symmetricStabilizationArrows = NativeK.omegaTests s :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests s

/-- Every original localizing map passes its original derived mapping tests. -/
theorem symmetricStabilizationArrows_localEquivalence (l : CategoryTheory.Operad.SmallFinBijGroupoid ×
  CategoryTheory.Operad.SmallFinBijGroupoid) :
    localEquivalences symmetricStabilizationArrows (symmetricStabilizationArrows l).hom :=
  fun _E hE => hE.2 l

/-- The entire localized right class is the original paired K-right class. -/
theorem symmetricLocalizedFibrations_eq_KRight :
    localizedFibrations symmetricStabilizationArrows = (NativeK.generators s).rlp := by
  unfold localizedFibrations
  rw [Native.cofibrations_eq, symmetricLocalEquivalences_eq_omegaTests,
    ← symmetric_left_class_eq]
  exact (NativeK.generators s).rlp_llp_rlp

/-- Original recognition supplies the complete local trivial-fibration class. -/
theorem symmetricLocalizedTrivialFibrations_eq_level :
    localizedFibrations symmetricStabilizationArrows ⊓
        localEquivalences symmetricStabilizationArrows = trivialFibrations C.{u, v} := by
  rw [symmetricLocalizedFibrations_eq_KRight, symmetricLocalEquivalences_eq_omegaTests,
    ← symmetric_right_class_eq]
  exact Native.Data.generatorsI_rlp

/-- The default terminal arrow and original zero arrow have the same actual K lifting. -/
theorem symmetricLocalized_terminal_iff_isOmega (X : C.{u, v}) :
    localizedFibrations symmetricStabilizationArrows (terminal.from X) ↔ NativeK.IsOmega s X := by
  rw [symmetricLocalizedFibrations_eq_KRight]
  let e := Diagrams.zeroDiagramIsTerminal.uniqueUpToIso (terminalIsTerminal (C := C.{u, v}))
  have h : Diagrams.toZero X ≫ e.hom = terminal.from X :=
    (terminalIsTerminal (C := C.{u, v})).hom_ext _ _
  let d : CategoryTheory.Arrow.mk (Diagrams.toZero X) ≅ CategoryTheory.Arrow.mk (terminal.from X) :=
    CategoryTheory.Arrow.isoMk (Iso.refl X) e ((Category.id_comp _).trans h.symm)
  exact ((NativeK.generators s).rlp.arrow_mk_iso_iff d).symm.trans
    (NativeK.lifting_toZero_iff_isOmega s X)

/-- The original full factor record proves the localized weak factorization system. -/
theorem symmetricLocalized_wfs :
    IsWeakFactorizationSystem
      (cofibrations C.{u, v} ⊓ localEquivalences symmetricStabilizationArrows)
      (localizedFibrations symmetricStabilizationArrows) := by
  rw [Native.cofibrations_eq, symmetricLocalEquivalences_eq_omegaTests,
    symmetricLocalizedFibrations_eq_KRight, ← symmetric_left_class_eq]
  exact OriginalGeneratedModel.weakFactorizationSystemOfGiven
    (NativeK.generators s) (NativeK.factorizationData s)

/-- Genuine original recognition constructs the full left Bousfield localization packet. -/
def symmetricLeftBousfieldLocalizationData :
    LeftBousfieldLocalizationData symmetricStabilizationArrows where
  localizingMaps := symmetricStabilizationArrows_localEquivalence
  baseWeak_le := by
    rw [symmetricLocalEquivalences_eq_omegaTests]
    exact NativeK.levelWeak_le_omegaTests s
  two_out_of_three := by
    rw [symmetricLocalEquivalences_eq_omegaTests]
    infer_instance
  retracts := by
    rw [symmetricLocalEquivalences_eq_omegaTests]
    infer_instance
  localized_wfs := symmetricLocalized_wfs
  trivialFibrations_eq := symmetricLocalizedTrivialFibrations_eq_level
  fibrant_iff X :=
    (symmetricLocalized_terminal_iff_isOmega X).trans
      (symmetricLocalFibrant_iff_isOmega X).symm
  weakEquivalence_iff_of_local f hX hY := by
    rw [symmetricLocalEquivalences_eq_omegaTests]
    exact NativeK.omegaTests_iff_levelWeak_of_isOmega s f
      ((symmetricLocalFibrant_iff_isOmega _).mp hX)
      ((symmetricLocalFibrant_iff_isOmega _).mp hY)

/-- The actual canonical stable weak class is the same derived local-equivalence class. -/
theorem symmetricStableWeak_eq_localEquivalences :
    symmetricModelCategory.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      localEquivalences symmetricStabilizationArrows :=
  symmetricLocalEquivalences_eq_omegaTests.symm

/-- The actual canonical stable right class is the original localized right class. -/
theorem symmetricStableFibrations_eq_localized :
    symmetricModelCategory.{u, v}.categoryWithFibrations.fibrations =
      localizedFibrations symmetricStabilizationArrows :=
  symmetricLocalizedFibrations_eq_KRight.symm

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction
