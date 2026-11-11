/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.DetectionPower
import Mathlib.Tactic.NormNum

/-! Tests for ABSOLUTE detection power: a worked case `n = 2`, `p₀ = 1/2`, `FPR = 1/8`, where
the critical count is `3`, the randomization is `1/2` at the boundary point `k - 1 = 2`, and
the size is exactly `1/8`; the PMC reading of Eq. 9 (randomization at `k`) has size `0`
instead. Also monotonicity in the allelic fraction, purity and copy number. -/

namespace MathlibExtTest.Biology.CancerGenomics.DetectionPower

open Finset MathlibExt.Biology.CancerGenomics.DetectionPower
  MathlibExt.Biology.CancerGenomics.Absolute

/-! ### Binomial law -/

example : binomPmf 2 (1 / 2) 2 = 1 / 4 := by norm_num [binomPmf]

example : binomPmf 2 (1 / 2) 3 = 0 := binomPmf_eq_zero _ (by norm_num)

example : ∑ i ∈ range 3, binomPmf 2 (1 / 3) i = 1 := sum_binomPmf 2 _

theorem tail1 : upperTail 2 (1 / 2) 1 = 3 / 4 := by
  rw [upperTail_eq_one_sub_sum]; norm_num [binomPmf, sum_range_succ]

theorem tail2 : upperTail 2 (1 / 2) 2 = 1 / 4 := by
  rw [upperTail_eq_one_sub_sum]; norm_num [binomPmf, sum_range_succ]

theorem tail3 : upperTail 2 (1 / 2) 3 = 0 := upperTail_eq_zero _ (by norm_num)

example : upperTail 2 (1 / 4) 1 ≤ upperTail 2 (1 / 2) 1 :=
  upperTail_mono (by norm_num) (by norm_num) (by norm_num) 1

/-! ### The worked test -/

theorem crit : criticalCount 2 (1 / 2) (1 / 8) = 3 := by
  apply le_antisymm (criticalCount_le (by norm_num))
  unfold criticalCount
  refine le_csInf ⟨3, show upperTail 2 (1 / 2) 3 ≤ 1 / 8 by rw [tail3]; norm_num⟩ fun m hm => ?_
  by_contra h
  have h2 : m ≤ 2 := by omega
  have := upperTail_antitone (n := 2) (p := 1 / 2) (by norm_num) (by norm_num) h2
  simp only [Set.mem_ofPred_eq] at hm
  rw [tail2] at this
  linarith

theorem rand : randomization 2 (1 / 2) (1 / 8) = 1 / 2 := by
  rw [randomization, crit, show 3 - 1 = 2 from rfl, tail2, tail3]; norm_num

/-- The exact-size reading: size `1/8` (`= 0 + (1/2) · Binom(2 | 2, 1/2)`). -/
example : power 2 (1 / 2) (1 / 8) (1 / 2) = 1 / 8 := power_self (by norm_num) (by norm_num)

example : power 2 (1 / 2) (1 / 8) (1 / 2) =
    upperTail 2 (1 / 2) 3 + (1 / 2) * binomPmf 2 (1 / 2) 2 := by
  rw [power, crit, rand]

/-- The PMC rendering of Eq. 9 (randomization multiplying `Binom(k | n, f)`) would give size
`0 ≠ 1/8` here, so it is not an exact-size test. -/
example : upperTail 2 (1 / 2) (criticalCount 2 (1 / 2) (1 / 8)) +
    randomization 2 (1 / 2) (1 / 8) * binomPmf 2 (1 / 2) (criticalCount 2 (1 / 2) (1 / 8)) ≠
      1 / 8 := by
  rw [crit, rand, tail3, binomPmf_eq_zero _ (by norm_num)]; norm_num

example : 0 ≤ randomization 2 (1 / 2) (1 / 8) ∧ randomization 2 (1 / 2) (1 / 8) < 1 :=
  randomization_mem (by norm_num) (by norm_num)

/-! ### Monotonicity -/

example : power 2 (1 / 2) (1 / 8) (1 / 2) ≤ power 2 (1 / 2) (1 / 8) (3 / 4) :=
  power_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Purity `1/4 → 1/2` at a diploid locus raises power. -/
example : power 30 (1 / 3000) (1 / 1000) (somaticAF (1 / 4) 2 1) ≤
    power 30 (1 / 3000) (1 / 1000) (somaticAF (1 / 2) 2 1) :=
  power_somaticAF_mono_purity (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Copy number `2 → 6` at purity `1/2` lowers power (Carter et al.'s motivating example). -/
example : power 30 (1 / 3000) (1 / 1000) (somaticAF (1 / 2) 6 1) ≤
    power 30 (1 / 3000) (1 / 1000) (somaticAF (1 / 2) 2 1) :=
  power_somaticAF_anti_copy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `FPR ≥ 1` is outside the domain: the critical count is `0` and `k - 1` is a truncated
`0`, so `power_self` is not claimed there. -/
example : criticalCount 2 (1 / 2) 1 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (by simp [upperTail_zero]))

end MathlibExtTest.Biology.CancerGenomics.DetectionPower
