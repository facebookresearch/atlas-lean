/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure

/-!
# Level fibrancy of sequential spectra

Identifies fibrancy in the sequential level model with fibrancy at every level. For pointed CGWH
coefficients, proves that every sequential spectrum is fibrant in that model.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Sequential

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Fibrancy in the direct shared-factory level model is actual enriched level fibrancy. -/
theorem level_isFibrant_iff (X : Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    IsFibrant X ↔ ∀ n : ℕ,
      IsFibrant
        (CategoryTheory.Spectra.Sequential.level (K := PointedCGWH.sphereOne.{u, v}) X n) := by
  let _ : ModelCategory Spectrum.{u, v} := levelModel
  change Fibration (terminal.from X) ↔ ∀ n : ℕ,
    IsFibrant (CategoryTheory.Spectra.Sequential.level (K := PointedCGWH.sphereOne.{u, v}) X n)
  have hClass : Fibration (terminal.from X) ↔
      fibrations Spectrum.{u, v} (terminal.from X) :=
    HomotopicalAlgebra.fibration_iff (terminal.from X)
  have hIndexed : fibrations Spectrum.{u, v} (terminal.from X) ↔
      ∀ a : Index.{u, v}, fibrations PointedCGWH.{u, v}
        ((EnrichedFunctorCat.evaluation a).map (terminal.from X)) := by
    change (levelModel.{u, v}).categoryWithFibrations.fibrations (terminal.from X) ↔ _
    have hChosen := congrArg
      (fun P : MorphismProperty Spectrum.{u, v} => P (terminal.from X))
      (levelModel_fibrations.{u, v})
    exact (iff_of_eq hChosen).trans
      (HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff _ _ _)
  have hLevels : (∀ a : Index.{u, v}, fibrations PointedCGWH.{u, v}
        ((EnrichedFunctorCat.evaluation a).map (terminal.from X))) ↔
      ∀ n : ℕ, fibrations PointedCGWH.{u, v}
        ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n).map
          (terminal.from X)) := by
    constructor
    · intro h n
      exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree
        PointedCGWH.sphereOne.{u, v} n)
    · intro h a
      exact h a.degree
  apply ((hClass.trans hIndexed).trans hLevels).trans
  have hTerminal (n : ℕ) : IsTerminal
      ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n).obj
        (⊤_ Spectrum.{u, v})) := by
    letI : PreservesLimitsOfSize.{0, 0}
        (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n) :=
      (CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction
        PointedCGWH.sphereOne.{u, v} n).rightAdjoint_preservesLimits
    exact IsTerminal.isTerminalObj
      (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n)
      (⊤_ Spectrum.{u, v}) terminalIsTerminal
  constructor
  · intro h n
    have hp : Fibration
        ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n).map
          (terminal.from X)) := (HomotopicalAlgebra.fibration_iff _).mpr (h n)
    exact (isFibrant_iff_of_isTerminal _ (hTerminal n)).mpr hp
  · intro h n
    have hp : Fibration
        ((CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n).map
          (terminal.from X)) := (isFibrant_iff_of_isTerminal _ (hTerminal n)).mp (h n)
    exact (HomotopicalAlgebra.fibration_iff _).mp hp

/-- Every canonical native sequential spectrum is fibrant in the chosen projective level model. -/
theorem level_allObjectsFibrant (X : Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    IsFibrant X := by
  let _ : ModelCategory Spectrum.{u, v} := levelModel
  exact (level_isFibrant_iff X).mpr
    (fun n => PointedCGWH.modelCategory.allObjectsFibrant
      (CategoryTheory.Spectra.Sequential.level (K := PointedCGWH.sphereOne.{u, v}) X n))

end PointedCGWH.Spectra.Sequential
