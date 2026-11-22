/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Existence

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.MeasureTheory.OptimalTransport.Existence

namespace MathlibExtTest.MeasureTheory.OptimalTransport.Existence

/-- An optimal coupling for the cost `|x - y|` between two probability measures on `ℝ`. -/
example (μ ν : ProbabilityMeasure ℝ) :
    ∃ π : ProbabilityMeasure (ℝ × ℝ), IsCoupling μ ν π ∧
      ∀ π' : ProbabilityMeasure (ℝ × ℝ), IsCoupling μ ν π' →
        ∫⁻ z, edist z.1 z.2 ∂(π : Measure (ℝ × ℝ)) ≤
          ∫⁻ z, edist z.1 z.2 ∂(π' : Measure (ℝ × ℝ)) :=
  exists_isCoupling_forall_lintegral_le μ ν continuous_edist

/-- The quadratic transport cost between `δ_0` and `δ_1` is attained, with value `1`. -/
example : ∃ π : ProbabilityMeasure (ℝ × ℝ),
    IsCoupling ⟨Measure.dirac (0 : ℝ), inferInstance⟩ ⟨Measure.dirac (1 : ℝ), inferInstance⟩ π ∧
      ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π : Measure (ℝ × ℝ)) = 1 := by
  obtain ⟨π, hπ, h⟩ := exists_isCoupling_lintegral_eq_transportCost (2 : ℝ)
    (⟨Measure.dirac (0 : ℝ), inferInstance⟩ : ProbabilityMeasure ℝ)
    ⟨Measure.dirac (1 : ℝ), inferInstance⟩
  refine ⟨π, hπ, ?_⟩
  have hW := wasserstein_dirac (p := 2) (by norm_num) (0 : ℝ) 1
  change transportCost 2 _ _ ^ (1 / (2 : ℝ)) = _ at hW
  have hT : transportCost 2 (⟨Measure.dirac (0 : ℝ), inferInstance⟩ : ProbabilityMeasure ℝ)
      ⟨Measure.dirac (1 : ℝ), inferInstance⟩ = edist (0 : ℝ) 1 ^ (2 : ℝ) := by
    rw [← hW, ← ENNReal.rpow_mul]; norm_num
  rw [h, hT, edist_dist, Real.dist_eq]
  norm_num

end MathlibExtTest.MeasureTheory.OptimalTransport.Existence
