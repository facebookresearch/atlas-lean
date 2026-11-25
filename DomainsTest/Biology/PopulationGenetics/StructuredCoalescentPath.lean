/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.StructuredCoalescentPath

/-! Tests for the path-space form of the island-pair mean coalescence times: the Q-matrix
entries on the smallest model (`d = 2`, `M = 1`), the path means `T₀ = 2`, `T₁ = 3` as
instances of the general theorems, and the no-migration boundary guards. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.StructuredCoalescentPath

open MathlibExt.Biology.PopulationGenetics.StructuredCoalescent
open MathlibExt.Biology.PopulationGenetics.StructuredCoalescentPath
open PairState

variable [MeasurableSpace PairState] [DiscreteMeasurableSpace PairState]

/-- Two demes, `M = 1`: exit rates are `2` (same), `1` (different), `0` (coalesced). -/
example : exitRate 2 1 same = 2 ∧ exitRate 2 1 different = 1 ∧
    exitRate 2 1 coalesced = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [exitRate, PairState.sum_eq, rate]

/-- Two demes, `M = 1`: the Q-matrix rows sum to zero and the diagonal is `-exitRate`. -/
example : rateMatrix 2 1 same same = -2 ∧ rateMatrix 2 1 same coalesced = 1 ∧
    rateMatrix 2 1 different same = 1 ∧ rateMatrix 2 1 coalesced coalesced = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [rateMatrix, exitRate, PairState.sum_eq, rate]

/-- Two demes, `M = 1`: the path mean from the same deme is `2`. -/
example : ∫⁻ ω, ctmcHittingTime (rateMatrix 2 1) same {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix (d := 2) (M := 1) (by norm_num) (by norm_num)) =
    ENNReal.ofReal 2 :=
  lintegral_coalescenceTime_same (by norm_num) (by norm_num)

/-- Two demes, `M = 1`: the path mean from different demes is `3`. -/
example : ∫⁻ ω, ctmcHittingTime (rateMatrix 2 1) different {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix (d := 2) (M := 1) (by norm_num) (by norm_num)) =
    ENNReal.ofReal 3 := by
  have h := lintegral_coalescenceTime_different (d := 2) (M := 1) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- No migration: from different demes the mean is infinite, from the same deme it is `1`. -/
example : (∫⁻ ω, ctmcHittingTime (rateMatrix 2 0) different {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix (d := 2) (M := 0) (by norm_num) le_rfl) = ∞) ∧
    (∫⁻ ω, ctmcHittingTime (rateMatrix 2 0) same {PairState.coalesced} ω
      ∂ctmcInputMeasure (isRateMatrix_rateMatrix (d := 2) (M := 0) (by norm_num) le_rfl) = 1) :=
  ⟨lintegral_coalescenceTime_different_zero (by norm_num),
   lintegral_coalescenceTime_same_zero (by norm_num)⟩

end MathlibExtTest.Biology.PopulationGenetics.StructuredCoalescentPath
