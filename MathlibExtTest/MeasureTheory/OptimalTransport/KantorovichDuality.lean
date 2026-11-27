/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.OptimalTransport.KantorovichDuality

open MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal
open MathlibExt.MeasureTheory.KantorovichDualityWanted
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (isCoupling_prod)

namespace MathlibExtTest.MeasureTheory.OptimalTransport.KantorovichDuality

/-- A cost infinite everywhere has unbounded dual values even for probability measures. -/
example (μ ν : ProbabilityMeasure ℝ) :
    (⨆ (ψ : ℝ →ᵇ ℝ) (φ : ℝ →ᵇ ℝ) (_ : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ ⊤),
      ENNReal.ofReal (∫ y, φ y ∂(ν : Measure ℝ) - ∫ x, ψ x ∂(μ : Measure ℝ))) = ⊤ := by
  rw [← kantorovich_duality_lsc μ ν (fun _ => ⊤) lowerSemicontinuous_const]
  simp

/-- Charging one unit on the open half-plane x > 0 gives the first marginal's mass there. -/
example (μ ν : ProbabilityMeasure ℝ) :
    (⨆ (ψ : ℝ →ᵇ ℝ) (φ : ℝ →ᵇ ℝ) (_ : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤
        (Prod.fst ⁻¹' Ioi (0 : ℝ) : Set (ℝ × ℝ)).indicator 1 (x, y)),
      ENNReal.ofReal (∫ y, φ y ∂(ν : Measure ℝ) - ∫ x, ψ x ∂(μ : Measure ℝ))) =
      (μ : Measure ℝ) (Ioi 0) := by
  let U : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_Ioi.preimage continuous_fst
  rw [← kantorovich_duality_lsc μ ν (U.indicator 1) (hU.lowerSemicontinuous_indicator zero_le)]
  have cost (π : ProbabilityMeasure (ℝ × ℝ)) (hπ : IsCoupling μ ν π) :
      ∫⁻ z, U.indicator 1 z ∂(π : Measure (ℝ × ℝ)) = (μ : Measure ℝ) (Ioi 0) := by
    rw [lintegral_indicator_one hU.measurableSet, hπ.1, Measure.map_apply measurable_fst
      measurableSet_Ioi]
  exact le_antisymm
    (iInf_le_of_le (μ.prod ν) (iInf_le_of_le (isCoupling_prod μ ν)
      (cost _ (isCoupling_prod μ ν)).le))
    (le_iInf₂ fun π hπ => (cost π hπ).ge)

end MathlibExtTest.MeasureTheory.OptimalTransport.KantorovichDuality
