/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoundedShiftedFractionResiduesFloorQuotientOddCountAsymptotic

/-! # Tests for `RoundedShiftedFractionResiduesFloorQuotientOddCountAsymptotic` -/

namespace MathlibExtTest.NumberTheory.RoundedShiftedFractionResiduesFloorQuotientOddCountAsymptotic

open MetaMathlibExt Filter Topology

-- At `n = 10` the count equals `7`, so the asymptotic bound gives a concrete inequality.
example : ∃ C : ℝ, |(7 : ℝ) - 10 * Real.log 2| ≤ C * Real.sqrt 10 := by
  obtain ⟨C, hC⟩ := floorQuotientOddCount_asymptotic.1
  refine ⟨C, ?_⟩
  have h10 := hC 10 (by decide)
  rw [floorQuotientOddCount_ten] at h10
  simpa using h10

-- The relative error tends to zero.
example : Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n - Real.log 2) atTop
    (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
    tendsto_const_nhds
  have h := floorQuotientOddCount_asymptotic.2.sub hconst
  rwa [sub_self] at h

end MathlibExtTest.NumberTheory.RoundedShiftedFractionResiduesFloorQuotientOddCountAsymptotic
