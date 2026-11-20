/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.WassersteinConvergence

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinConvergence

/-- The Dirac probability measure at a real number. -/
noncomputable def δ (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩

/-- `δ_{1/(k+1)} → δ_0` weakly, deduced from `W_1(δ_{1/(k+1)}, δ_0) = 1/(k+1) → 0`. -/
example : Tendsto (fun k : ℕ => δ (1 / ((k : ℝ) + 1))) atTop (𝓝 (δ 0)) := by
  refine tendsto_of_tendsto_wasserstein le_rfl ?_
  simp only [δ, wasserstein_dirac one_pos]
  exact (tendsto_iff_edist_tendsto_0).1 tendsto_one_div_add_atTop_nhds_zero_nat

end MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinConvergence
