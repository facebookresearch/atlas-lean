/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalModel
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.LocalizingImages
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic

/-!
# Conditional localization at the original orthogonal stabilization arrows

The same exact original comparison Hom-bijection proposition supplies the
right-class recognition needed for the two weak factorization systems.
The already proved native derived mapping comparison identifies local
equivalences with the complete original Omega Hom tests. These genuine
class laws construct localization data for the unchanged Arrow family.

The localizing arrows retain both original indices, coefficients and
inclusions. The original native level model, its realized cardinal and the
caller's ordinal bottom remain fixed. No localization record or desired
stable model is an input. The original comparison proposition remains
explicit, so this is a conditional helper rather than a native existence
theorem without hypotheses.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat MonoidalCategory HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalization

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The exact full original orthogonal Arrow function, at every actual pair. -/
abbrev originalArrows : ℕ × ℕ → CategoryTheory.Arrow C.{u, v} :=
  DerivedLocalMapping.stabilizationArrows orthogonalFamily

omit B in
/-- Each complete original source is the actual added-degree sphere free object. -/
theorem originalArrows_left (l : ℕ × ℕ) :
    (originalArrows.{u, v} l).left =
      Free.object (orthogonalFamily.target l) (orthogonalFamily.coefficient l) := rfl

omit B in
/-- Each complete original target is the original source-degree unit free object. -/
theorem originalArrows_right (l : ℕ × ℕ) :
    (originalArrows.{u, v} l).right =
      Free.object (orthogonalFamily.source l) (𝟙_ PointedCGWH.{u, v}) := rfl

omit B in
/-- The original inclusion and coefficient give the same actual stabilization map. -/
theorem originalArrows_hom (l : ℕ × ℕ) :
    (originalArrows.{u, v} l).hom = NativeK.stabilization orthogonalFamily l := rfl

/-- Derived local equivalences are the entire original native Omega Ho-test class. -/
theorem localEquivalences_eq :
    localEquivalences originalArrows.{u, v} = stableWeakEquivalences :=
  DerivedLocalMapping.localEquivalences_eq_omegaTests orthogonalFamily

/-- Local trivial cofibrations are the same full ordinary cofibration intersection. -/
theorem localTrivialCofibrations_eq :
    cofibrations C.{u, v} ⊓ localEquivalences originalArrows =
      stableTrivialCofibrations := by
  rw [localEquivalences_eq, ← stableCofibrations_eq_level]

/-- Every actual original label is locally weak by its original mapping-end transpose. -/
theorem originalArrows_localEquivalence (l : ℕ × ℕ) :
    localEquivalences originalArrows.{u, v} (originalArrows l).hom := by
  rw [localEquivalences_eq]
  exact IndexKan.originalStabilization_omegaTests orthogonalFamily l

/-- Conditional right-class recognition identifies the full localized right property. -/
theorem localizedFibrations_eq
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    localizedFibrations originalArrows.{u, v} = stableFibrations := by
  change (cofibrations C ⊓ localEquivalences originalArrows).rlp = stableFibrations
  rw [localTrivialCofibrations_eq]
  let _ : IsWeakFactorizationSystem stableTrivialCofibrations stableFibrations :=
    ConditionalModel.conditional_K_wfs hComparison
  exact rlp_eq_of_wfs stableTrivialCofibrations stableFibrations

/-- The localized weak factorization system is the same actual original paired K system. -/
theorem localized_wfs (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    IsWeakFactorizationSystem
      (cofibrations C.{u, v} ⊓ localEquivalences originalArrows)
      (localizedFibrations originalArrows) := by
  rw [localTrivialCofibrations_eq, localizedFibrations_eq hComparison]
  exact ConditionalModel.conditional_K_wfs hComparison

/-- Its full trivial-right property is exactly the unchanged original level one. -/
theorem localizedTrivialFibrations_eq
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    localizedFibrations originalArrows.{u, v} ⊓ localEquivalences originalArrows =
      trivialFibrations C := by
  rw [localizedFibrations_eq hComparison, localEquivalences_eq]
  change stableTrivialFibrations = trivialFibrations C
  rw [← ConditionalRecognition.right_class_eq hComparison]
  exact HomotopicalAlgebra.EnrichedProjective.Native.Data.generatorsI_rlp

/-- The full K-right terminal criterion is independent of the chosen terminal object. -/
theorem stableFibrations_terminal_iff_isOmega (X : C.{u, v}) :
    stableFibrations (terminal.from X) ↔ NativeK.IsOmega orthogonalFamily X := by
  let e : ⊤_ C.{u, v} ≅ Diagrams.zeroDiagram (A := O.{u, v}) :=
    terminalIsTerminal.uniqueUpToIso (Diagrams.zeroDiagramIsTerminal (A := O.{u, v}))
  let a : CategoryTheory.Arrow.mk (terminal.from X) ≅
      CategoryTheory.Arrow.mk (Diagrams.toZero X) :=
    CategoryTheory.Arrow.isoMk' _ _ (Iso.refl X) e
      (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)
  exact (stableFibrations.arrow_mk_iso_iff a).trans
    (NativeK.lifting_toZero_iff_isOmega orthogonalFamily X)

/-- Localized fibrancy is exactly the original full-family Omega condition. -/
theorem localizedFibrations_terminal_iff_isOmega
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) (X : C.{u, v}) :
    localizedFibrations originalArrows (terminal.from X) ↔
      NativeK.IsOmega orthogonalFamily X := by
  rw [localizedFibrations_eq hComparison]
  exact stableFibrations_terminal_iff_isOmega X

/-- The original all-target Ho tests give the actual local Whitehead statement. -/
theorem localEquivalence_iff_levelWeak_of_local
    {X Y : C.{u, v}} (f : X ⟶ Y)
    (hX : isLocalFibrant originalArrows X) (hY : isLocalFibrant originalArrows Y) :
    localEquivalences originalArrows f ↔ weakEquivalences C f := by
  rw [localEquivalences_eq]
  exact NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily f
    ((DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily X).mp hX)
    ((DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily Y).mp hY)

/-- All actual localization fields are proved from the same explicit original comparison.
The original Arrow function and native level model are the literal input family and base. -/
theorem data (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    LeftBousfieldLocalizationData originalArrows.{u, v} := by
  exact
    { localizingMaps := originalArrows_localEquivalence
      baseWeak_le := by
        rw [localEquivalences_eq]
        exact levelWeak_le_stableWeakEquivalences
      two_out_of_three := by
        rw [localEquivalences_eq]
        infer_instance
      retracts := by
        rw [localEquivalences_eq]
        infer_instance
      localized_wfs := localized_wfs hComparison
      trivialFibrations_eq := localizedTrivialFibrations_eq hComparison
      fibrant_iff X :=
        (localizedFibrations_terminal_iff_isOmega hComparison X).trans
          (DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily X).symm
      weakEquivalence_iff_of_local := localEquivalence_iff_levelWeak_of_local }

/-- The family-indexed carrier is keyed by the proved data for these same original arrows. -/
abbrev Carrier (hComparison : ComparisonHomBijections.{u, v} (B := B)) :=
  LeftLocalized (data hComparison)

/-- Proof-term independence concerns the same explicit comparison proposition. -/
theorem data_proof_irrel (h h' : ComparisonHomBijections.{u, v} (B := B)) :
    data h = data h' := rfl

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalization
