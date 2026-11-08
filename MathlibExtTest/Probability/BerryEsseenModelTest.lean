/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BerryEsseenModel

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel
open scoped ENNReal NNReal

namespace MathlibExtTest.BerryEsseenModel

example : IsStandardizedLaw (gaussianReal 0 1) := standardGaussian_isStandardized

example (μ : Measure ℝ) :
    MemLp id 3 μ ↔ Integrable (fun x : ℝ ↦ |x| ^ 3) μ :=
  memLp_three_iff_integrable_absCube μ

example : 0 < thirdMoment (gaussianReal 0 1) :=
  thirdMoment_positive standardGaussian_isStandardized

example : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i)
    (iidLaw (gaussianReal 0 1)) := iidLaw_independent standardGaussian_isStandardized

example (i : ℕ) : (iidLaw (gaussianReal 0 1)).map (fun ω ↦ ω i) = gaussianReal 0 1 :=
  iidLaw_map_eval standardGaussian_isStandardized i

example (x : ℝ) :
    cdf (normalizedLaw (gaussianReal 0 1) ⟨1, by decide⟩) x = normalCDF x := by
  rw [normalizedLaw_one standardGaussian_isStandardized]
  rfl

example : kolmogorovError (gaussianReal 0 1) ⟨1, by decide⟩ = 0 :=
  standardGaussian_error_one

example (μ : Measure ℝ) (n : ℕ+) : 0 ≤ kolmogorovError μ n :=
  kolmogorovError_nonnegative μ n

example (μ : Measure ℝ) (n : ℕ+) : kolmogorovError μ n ≤ 1 :=
  kolmogorovError_le_one μ n

end MathlibExtTest.BerryEsseenModel

#eval "C19 canonical Gaussian, positive sample and actual error proofs elaborated"
