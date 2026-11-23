/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry1Powersum

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry1Powersum

open Asymptotics Filter Topology
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum

-- For reciprocal square roots, the full one-term expansion has error tending to zero.
example :
    Tendsto
      (fun n : ℕ => chapter7PowerSum ((-1 / 2 : ℝ) : ℂ) n -
        chapter7Entry1Approx ((-1 / 2 : ℝ) : ℂ) 1 n)
      atTop (𝓝 0) := by
  have hO := ramanujan_part1_ch7_entry1_powersum ((-1 / 2 : ℝ) : ℂ) 1
    (by norm_num) (by norm_num) (by norm_num)
  apply hO.trans_tendsto
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  rw [Real.rpow_eq_pow]
  norm_num

-- For the sum of the first n integers, the one-term expansion has error tending to zero.
example :
    Tendsto
      (fun n : ℕ => chapter7PowerSum 1 n - chapter7Entry1Approx 1 1 n)
      atTop (𝓝 0) := by
  have hO := ramanujan_part1_ch7_entry1_powersum (1 : ℂ) 1
    (by norm_num) (by norm_num) (by norm_num)
  apply hO.trans_tendsto
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  rw [Real.rpow_eq_pow]
  norm_num

-- The falling product gains one factor per step.
example (r : ℂ) : chapter7FallingGammaRatio r 2 = r * (r - 1) := by
  rw [chapter7FallingGammaRatio_succ, chapter7FallingGammaRatio_succ,
    chapter7FallingGammaRatio_zero]
  push_cast
  ring

-- With no Bernoulli corrections the remainder coefficient is the exponent itself.
example : powerSumRemainderFactor 0 (-1 / 2) = -1 / 2 := by
  simp

-- With one correction it is `r (r - 1) (r - 2) / 3!`.
example (r : ℂ) : powerSumRemainderFactor 1 r = r * (r - 1) * (r - 2) / 6 := by
  rw [powerSumRemainderFactor_eq]
  simp [chapter7FallingGammaRatio_succ, Nat.factorial]

-- The tail is the improper integral of the odd kernel against `x ^ (r - (2 * N + 1))`.
example (n : ℕ) :
    powerSumTail 1 (1 / 2) n =
      ∫ x : ℝ in Set.Ioi (n : ℝ),
        (x : ℂ) ^ ((1 / 2 : ℂ) - 3) * (MetaMathlibExt.bernoulliKernel 3 x : ℂ) := by
  rw [powerSumTail_eq_integral]
  norm_num

-- At `r = 1`, `N = 1`, `n = 2` the remainder coefficient vanishes, so the exact expansion reads
-- `1 + 2 = ζ(-1) + 2 + 1 + 1 / 12` and recovers `ζ(-1) = -1 / 12`.
example : riemannZeta (-1) = -1 / 12 := by
  have h := chapter7PowerSum_exact_expansion 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hsum : chapter7PowerSum 1 2 = 3 := by
    rw [chapter7PowerSum, show Finset.Icc 1 2 = {1, 2} by decide]
    norm_num [chapter7NatCpow]
  have hfactor : powerSumRemainderFactor 1 1 = 0 := by
    simp [powerSumRemainderFactor_eq, chapter7FallingGammaRatio_succ]
  have hterm : ∑ j ∈ Finset.range 1, chapter7Entry1Term 1 2 j = 1 / 12 := by
    norm_num [chapter7Entry1Term, chapter7FallingGammaRatio_succ, chapter7NatCpow,
      bernoulli_two]
  rw [hsum, hfactor, hterm] at h
  norm_num [chapter7NatCpow] at h
  linear_combination -h

end MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry1Powersum
