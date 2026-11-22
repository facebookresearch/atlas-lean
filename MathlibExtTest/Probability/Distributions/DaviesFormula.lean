/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.DaviesFormula

/-! # Tests for `MathlibExt.Probability.Distributions.DaviesFormula`

Davies boundary: with all weights `0`, the Davies integral converges to the mid-p value `½` at
`q = 0`, not to `P(Q > 0) = 0`. For `χ²₁` (one unit weight) it converges to the exact upper tail
at every `q`. -/

open MeasureTheory Filter Topology Set
open MathlibExt.Analysis.WeightedChiSquare MathlibExt.Probability.Distributions.DaviesFormula

namespace MathlibExtTest.DaviesFormula

/-- With zero weights Davies' characteristic function is `1`. -/
example (t : ℝ) : daviesCharFun (0 : Fin 3 → ℝ) t = 1 := by simp [daviesCharFun]

/-- Every characteristic function is `1` at `t = 0`. -/
example (lam : Fin 2 → ℝ) : daviesCharFun lam 0 = 1 := by simp [daviesCharFun]

/-- Degenerate mixture: with all weights `0`, the Davies integral at `q = 0` converges to the
mid-p value `½`, while `P(Q > 0) = 0` and `P(Q ≥ 0) = 1`. -/
example : Tendsto (fun T => 1 / 2 + Real.pi⁻¹ * ∫ t in (0 : ℝ)..T,
    (Complex.exp (-(t * 0) * Complex.I) * daviesCharFun (0 : Fin 1 → ℝ) t).im / t) atTop
      (𝓝 (1 / 2)) := by
  have h := tendsto_davies (0 : Fin 1 → ℝ) 0
  have hv : ((weightedChiSq (0 : Fin 1 → ℝ)).real (Ioi 0) +
      (weightedChiSq (0 : Fin 1 → ℝ)).real (Ici 0)) / 2 = 1 / 2 := by
    simp [weightedChiSq_zero]
  rw [hv] at h
  exact h

/-- The exact tail of `P(Q > 0)` is `0` for the zero mixture, so the mid-p form is needed. -/
example : (weightedChiSq (0 : Fin 1 → ℝ)).real (Ioi 0) = 0 := by
  simp [weightedChiSq_zero]

/-- For `χ²₁` Davies' integral converges to the exact upper tail at every `q`. -/
example (q : ℝ) : Tendsto (fun T => 1 / 2 + Real.pi⁻¹ * ∫ t in (0 : ℝ)..T,
    (Complex.exp (-(t * q) * Complex.I) * daviesCharFun (fun _ : Fin 1 => (1 : ℝ)) t).im / t)
      atTop (𝓝 ((weightedChiSq fun _ : Fin 1 => (1 : ℝ)).real (Ioi q))) :=
  tendsto_davies_of_ne_zero (j := 0) one_ne_zero q

/-- `χ²₁` has no atoms. -/
example (q : ℝ) : weightedChiSq (fun _ : Fin 1 => (1 : ℝ)) {q} = 0 :=
  weightedChiSq_singleton (j := 0) one_ne_zero q

end MathlibExtTest.DaviesFormula
