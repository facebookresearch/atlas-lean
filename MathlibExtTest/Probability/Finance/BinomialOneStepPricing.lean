/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BinomialOneStepPricing
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.BinomialOneStepPricing`

* The numeric instance `S₀ = 100`, `u = 1.1`, `d = 0.9`, `R = 1.05`, `Cu = 10`, `Cd = 0`:
  `q = 3/4`, price `= 50/7`, delta `= 1/2`, bond holding `= -300/7`, cost `= 50/7`.
* The same instance through the landed `claimValue` and `hedgeRatio` at horizon `1`.
-/

@[expose] public section

open MathlibExt.Probability.Finance.BinomialOneStepPricing
open MathlibExt.Probability.Finance.BinomialReplication

namespace MathlibExtTest.Probability.Finance.BinomialOneStepPricing

example : rnProb (11 / 10) (9 / 10) (21 / 20) = 3 / 4 := by
  unfold rnProb
  norm_num

example : riskNeutralPrice (11 / 10) (9 / 10) (21 / 20) 10 0 = 50 / 7 := by
  unfold riskNeutralPrice rnProb
  norm_num

example : deltaHedge 100 (11 / 10) (9 / 10) 10 0 = 1 / 2 := by
  unfold deltaHedge
  norm_num

example : bondHolding (11 / 10) (9 / 10) (21 / 20) 10 0 = -300 / 7 := by
  unfold bondHolding
  norm_num

example : replicationCost 100 (11 / 10) (9 / 10) (21 / 20) 10 0 = 50 / 7 := by
  unfold replicationCost deltaHedge bondHolding
  norm_num

example : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [true] = 10 := by
  simp

example : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [false] = 0 := by
  simp

example :
    claimValue (11 / 10) (9 / 10) (21 / 20)
      (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) 1 [] = 50 / 7 := by
  have hCu : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [true] = 10 := by
    simp
  have hCd : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [false] = 0 := by
    simp
  rw [claimValue_one_eq_replicationCost (S₀ := 100) (Cu := 10) (Cd := 0) (by norm_num)
    (by norm_num) (by norm_num) hCu hCd]
  unfold replicationCost deltaHedge bondHolding
  norm_num

example :
    hedgeRatio 100 (11 / 10) (9 / 10) (21 / 20)
      (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) 1 [] = 1 / 2 := by
  have hCu : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [true] = 10 := by
    simp
  have hCd : (fun s : List Bool => if s = [true] then (10 : ℝ) else 0) [false] = 0 := by
    simp
  rw [hedgeRatio_one_eq_deltaHedge (Cu := 10) (Cd := 0) hCu hCd]
  unfold deltaHedge
  norm_num

end MathlibExtTest.Probability.Finance.BinomialOneStepPricing
