/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.HeatTransfer.HeatExchangers

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.HeatTransfer.HeatExchangers`

Two parallel-flow exchangers with `Ch = 3 kW/K`, `Cc = 3/2 kW/K`, `L = 2 m`, `Thi = 360 K` and
`Tci = 300 K`:

* `UA = log 2 kW/K`: outlets `350 K` and `320 K`, end differences `60` and `30`, logarithmic mean
  `30 / log 2`, and `UA ΔT_lm = 30 kW`, the heat lost by the hot stream;
* `UA = 0`: no exchange, and the logarithmic mean of the equal end differences takes its
  equal-difference branch instead of the junk value of `0 / log 1`.
-/

@[expose] public section

namespace PhyslibExtTest.HeatTransfer.HeatExchangers

open _root_.HeatTransfer.HeatExchangers

/-- `UA > 0` with unequal inlets, in kW/K, m and K: `Ch = 3`, `Cc = 3 / 2`, `L = 2`,
`UA = log 2 ≈ 0.693` (so `K = log 2 / 2` and `UA (1 / Ch + 1 / Cc) = log 2`), `Thi = 360`,
`Tci = 300`. The outlets are `Th(L) = 350` and `Tc(L) = 320`; the end differences `60` and `30`
have logarithmic mean `30 / log 2`, and `UA ΔT_lm = 30 kW = Ch (Thi - Th(L))`. -/
lemma fixture_parallel_unequal :
    parallelHotTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2 = 350 ∧
      parallelColdTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2 = 320 ∧
      logMeanTempDiff (360 - 300) (350 - 320) = 30 / Real.log 2 ∧
      Real.log 2 * logMeanTempDiff (360 - 300) (350 - 320) = 3 * (360 - 350) := by
  have hr : parallelDecayRate 3 (3 / 2) (Real.log 2 / 2) * 2 = Real.log 2 := by
    unfold parallelDecayRate
    field_simp
    ring
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hexp : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log h2pos]
    norm_num
  have e1 : (360 : ℝ) - 300 = 60 := by norm_num
  have e2 : (350 : ℝ) - 320 = 30 := by norm_num
  have h3 : logMeanTempDiff (360 - 300) (350 - 320) = 30 / Real.log 2 := by
    unfold logMeanTempDiff
    simp only [e1, e2]
    norm_num
  have h12 : (1 : ℝ) < 2 := by norm_num
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos h12)
  refine ⟨?_, ?_, h3, ?_⟩
  · unfold parallelHotTemp
    rw [hr, hexp]
    norm_num
  · unfold parallelColdTemp
    rw [hr, hexp]
    norm_num
  · rw [h3]
    field_simp
    ring

/-- `UA = 0` gives no exchange: with `K = 0` both streams keep their inlet temperatures
`360 K` and `300 K`, and the logarithmic mean of the equal end differences takes the
equal-difference branch `60`, while the unguarded formula `(Δ - Δ) / log (Δ / Δ)` divides by
`log 1 = 0` and returns Lean's junk value `0`. -/
lemma fixture_parallel_no_exchange :
    (∀ x, parallelHotTemp 3 (3 / 2) 0 360 300 x = 360 ∧
      parallelColdTemp 3 (3 / 2) 0 360 300 x = 300) ∧
      logMeanTempDiff (360 - 300) (360 - 300) = 60 ∧
      ((360 : ℝ) - 300 - (360 - 300)) / Real.log ((360 - 300) / (360 - 300)) = 0 := by
  have hr : ∀ x, parallelDecayRate 3 (3 / 2) 0 * x = 0 := by
    intro x
    unfold parallelDecayRate
    simp only [zero_mul]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · unfold parallelHotTemp
    unfold parallelColdTemp
    rw [hr x]
    constructor <;> simp only [neg_zero, Real.exp_zero, sub_self, mul_zero, sub_zero, add_zero]
  · unfold logMeanTempDiff
    norm_num
  · have h0 : ((360 : ℝ) - 300 - (360 - 300)) = 0 := by norm_num
    rw [h0]
    exact zero_div _

end PhyslibExtTest.HeatTransfer.HeatExchangers
