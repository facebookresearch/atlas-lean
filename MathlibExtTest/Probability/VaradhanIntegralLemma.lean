/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.VaradhanIntegralLemma

/-!
# Tests for Varadhan's integral lemma

Non-vacuity checks: the lemma applies to the Dirac LDP with a constant and with `Real.cos`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.VaradhanIntegralLemma

namespace MathlibExtTest.Probability.VaradhanIntegralLemma

/-- Dirac mass at `0` on `ℝ` with the constant function `F = 1`. -/
example : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * (fun _ : ℝ => (1 : ℝ)) x))
          ∂((fun _ => Measure.dirac (0 : ℝ)) n)))
      atTop (𝓝 (⨆ x : ℝ, (((1 : ℝ) : EReal) - (diracRate (0 : ℝ) x : EReal)))) :=
  tendsto_log_lintegral_exp (satisfiesLDP_dirac (0 : ℝ)) continuous_const
    (C := 1) (fun _ => by simp)

/-- Dirac mass at `0` on `ℝ` with `F = Real.cos`, bounded by `1`. -/
example : Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * Real.cos x))
          ∂((fun _ => Measure.dirac (0 : ℝ)) n)))
      atTop (𝓝 (⨆ x : ℝ, ((Real.cos x : EReal) - (diracRate (0 : ℝ) x : EReal)))) :=
  tendsto_log_lintegral_exp (satisfiesLDP_dirac (0 : ℝ)) Real.continuous_cos
    (fun x => Real.abs_cos_le_one x)

/-- The lower bound alone, for the lower semicontinuous (here continuous) `Real.sin`. -/
example : (⨆ x : ℝ, ((Real.sin x : EReal) - (diracRate (0 : ℝ) x : EReal))) ≤
    liminf (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (n * Real.sin x))
        ∂((fun _ => Measure.dirac (0 : ℝ)) n))) atTop :=
  le_liminf_log_lintegral_exp (satisfiesLDP_dirac (0 : ℝ))
    Real.continuous_sin.lowerSemicontinuous

end MathlibExtTest.Probability.VaradhanIntegralLemma
