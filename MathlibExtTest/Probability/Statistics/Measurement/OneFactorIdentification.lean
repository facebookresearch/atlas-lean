/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.OneFactorIdentification
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Statistics.Measurement

namespace MathlibExtTest.Probability.Statistics.Measurement.OneFactorIdentification

private def loadings : Fin 3 → ℝ := ![1, -2, 3]

-- Use a variance-one factor and zero errors to instantiate the random-variable model.
example : cov[loadings 0 • (id : ℝ → ℝ) + 0, loadings 1 • (id : ℝ → ℝ) + 0;
    gaussianReal 0 1] = -2 := by
  have h := one_factor_identification (P := gaussianReal 0 1) id
    (fun (_ : Fin 3) (_ : ℝ) => (0 : ℝ)) loadings (memLp_id_gaussianReal 2)
    (fun _ => memLp_const 0) (by simp)
    (fun _ => covariance_const_right 0) (fun _ _ _ => covariance_const_right 0)
  have h01 := h.2.1 0 1 (by decide)
  change cov[loadings 0 • (id : ℝ → ℝ) + 0, loadings 1 • (id : ℝ → ℝ) + 0;
    gaussianReal 0 1] = loadings 0 * loadings 1 at h01
  simpa [loadings] using h01

private def zeroLoadings : Fin 2 → ℝ := ![0, 1]

-- The covariance formula also applies to two indicators, one with zero loading.
example : cov[zeroLoadings 0 • (id : ℝ → ℝ) + 0, zeroLoadings 1 • (id : ℝ → ℝ) + 0;
    gaussianReal 0 1] = 0 := by
  have h := one_factor_identification (P := gaussianReal 0 1) id
    (fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) zeroLoadings (memLp_id_gaussianReal 2)
    (fun _ => memLp_const 0) (by simp)
    (fun _ => covariance_const_right 0) (fun _ _ _ => covariance_const_right 0)
  have h01 := h.2.1 0 1 (by decide)
  change cov[zeroLoadings 0 • (id : ℝ → ℝ) + 0, zeroLoadings 1 • (id : ℝ → ℝ) + 0;
    gaussianReal 0 1] = zeroLoadings 0 * zeroLoadings 1 at h01
  rw [h01]
  simp [zeroLoadings]

-- The counterexample holds with positive error variances and is not a sign flip.
example : ∃ (l ψ l' ψ' : Fin 3 → ℝ), l 0 = 0 ∧ l' 0 = 0 ∧
    (∀ i, 0 < ψ i ∧ 0 < ψ' i) ∧
    oneFactorCovariance l' ψ' = oneFactorCovariance l ψ ∧ l' ≠ l ∧ l' ≠ -l := by
  have h := one_factor_zero_loading_counterexample
  refine ⟨![0, 1, 1], ![1, 4, 1], ![0, 2, 1 / 2], ![1, 1, 7 / 4],
    rfl, rfl, ?_, h.2⟩
  intro i
  fin_cases i <;> norm_num

end MathlibExtTest.Probability.Statistics.Measurement.OneFactorIdentification
