/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.WignerOperatorNormOpNormConcentrationMedian

/-!
# One-sided operator norm concentration

The median concentration theorem gives an upper-tail bound with the same constants.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Proposition 2.3.10.
-/

namespace MathlibExtTest.Probability.WignerOperatorNormOpNormConcentrationMedian

open MeasureTheory ProbabilityTheory Real

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (M : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ i j, Measurable fun ω => M ω i j)
    (hind : iIndepFun (fun ij : Fin n × Fin n => fun ω => M ω ij.1 ij.2) P)
    (hmean : ∀ i j, ∫ ω, M ω i j ∂P = 0) (hbounded : ∀ i j ω, |M ω i j| ≤ 1)
    (m : ℝ)
    (hm₁ : 1 / 2 ≤ P.real {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖ ≤ m})
    (hm₂ : 1 / 2 ≤ P.real {ω | m ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}) :
    ∃ C > 0, ∃ c > 0, ∀ t : ℝ, 0 < t →
      P.real {ω | m + t ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖} ≤
        C * exp (-c * t ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ :=
    MathlibExt.Probability.WignerOperatorNormWanted.opNorm_concentration_median
  refine ⟨C, hC, c, hc, fun t ht => ?_⟩
  calc
    _ ≤ P.real {ω | t ≤ |‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖ - m|} := by
      refine measureReal_mono fun ω hω => ?_
      exact (le_sub_iff_add_le'.mpr hω).trans (le_abs_self _)
    _ ≤ C * exp (-c * t ^ 2) :=
      h Ω inferInstance P inferInstance n M hmeas hind hmean hbounded m hm₁ hm₂ t ht

end MathlibExtTest.Probability.WignerOperatorNormOpNormConcentrationMedian
