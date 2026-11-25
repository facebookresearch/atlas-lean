/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.OptimalTransport.KantorovichRubinstein

open MeasureTheory
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein_dirac)
open MathlibExt.MeasureTheory.WassersteinWanted (wasserstein_one_eq_iSup_lipschitz)

/-- On two Dirac masses, the Lipschitz supremum recovers the distance between their atoms. -/
example (a b : ℝ) :
    (⨆ (ψ : ℝ → ℝ) (_ : LipschitzWith 1 ψ), ENNReal.ofReal (ψ a - ψ b)) = edist a b := by
  let δ (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩
  have h (x : ℝ) : ∫⁻ y, edist (0 : ℝ) y ∂(δ x : Measure ℝ) < ∞ := by
    change ∫⁻ y, edist (0 : ℝ) y ∂Measure.dirac x < ∞
    rw [lintegral_dirac]
    exact edist_lt_top _ _
  have hdual := wasserstein_one_eq_iSup_lipschitz (δ a) (δ b) 0 (h a) (h b)
  rw [wasserstein_dirac (p := 1) one_pos a b] at hdual
  change edist a b = ⨆ (ψ : ℝ → ℝ) (_ : LipschitzWith 1 ψ),
    ENNReal.ofReal (∫ x, ψ x ∂Measure.dirac a - ∫ x, ψ x ∂Measure.dirac b) at hdual
  simpa only [integral_dirac] using hdual.symm
