/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.CorrelatedTwoFactor
import Mathlib.Tactic.NormNum

open Matrix
open MathlibExt.Probability.Statistics.Measurement

namespace MathlibExtTest.Probability.Statistics.Measurement.CorrelatedTwoFactor

private def lZero : Fin 5 → ℝ := ![1, 2, -3, 4, 0]
private def lFull : Fin 5 → ℝ := ![1, 2, -3, 4, 5]
private def ψ : Fin 5 → ℝ := fun _ => 1

-- Fixing the correlation recovers the final loading even when it is zero.
example : correlatedTwoFactorCov lZero ψ (1 / 4) 0 4 / (lZero 0 * (1 / 4)) = 0 := by
  have h := correlated_two_factor_identification lZero ψ (1 / 4)
    (by norm_num [lZero]) (by norm_num [lZero]) (by norm_num [lZero])
  have hz := (h.2.2.1 (by norm_num)).2
  rw [← hz]
  norm_num [lZero]

-- With both loadings present, the recovered correlation magnitude is independent of its sign.
example :
    let C := correlatedTwoFactorCov lFull ψ (-1 / 2)
    C 0 3 * C 0 4 / (lFull 0 ^ 2 * C 3 4) = 1 / 4 := by
  intro C
  have h := correlated_two_factor_identification lFull ψ (-1 / 2)
    (by norm_num [lFull]) (by norm_num [lFull]) (by norm_num [lFull])
  have hr := h.2.2.2.1 (by norm_num [lFull]) (by norm_num [lFull])
  change (-1 / 2 : ℝ) ^ 2 = C 0 3 * C 0 4 / (lFull 0 ^ 2 * C 3 4) at hr
  rw [← hr]
  norm_num

-- Rescaling by 1/2 changes the fourth loading and preserves the covariance at correlation 1/2.
example :
    correlatedTwoFactorCov ![1, 2, -3, 2, 0] ![1, 1, 1, 13, 1] (1 / 2) =
      correlatedTwoFactorCov lZero ψ (1 / 4) := by
  have h := correlated_two_factor_identification lZero ψ (1 / 4)
    (by norm_num [lZero]) (by norm_num [lZero]) (by norm_num [lZero])
  have hr := (h.2.2.2.2.2 (by norm_num [lZero]) (by norm_num [lZero])
    (fun _ => by norm_num [ψ]) (1 / 2) (by norm_num) (by norm_num)).1
  have hl : Function.update lZero 3 ((1 / 2) * lZero 3) = ![1, 2, -3, 2, 0] := by
    funext i
    fin_cases i <;> norm_num [lZero, Function.update_apply]
  have hψ : Function.update ψ 3 (ψ 3 + (1 - (1 / 2) ^ 2) * lZero 3 ^ 2) = ![1, 1, 1, 13, 1] := by
    funext i
    fin_cases i <;> norm_num [ψ, lZero, Function.update_apply]
  rw [hl, hψ] at hr
  convert hr using 2
  norm_num

end MathlibExtTest.Probability.Statistics.Measurement.CorrelatedTwoFactor
