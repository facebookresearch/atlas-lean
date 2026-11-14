/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.StatisticalTreatment
import Mathlib.Tactic.NormNum

/-!
# Statistical treatment checks

Instances pinning the pooled SD, outlier procedures, both LOD conventions, and
boundary cases (no claim at `n = 1`; no rejection on degenerate input).
-/

namespace Chemistry.StatisticalTreatmentTest

open Chemistry.StatisticalTreatment

@[expose] public section

-- Pooled-SD instance: n1 = 5 with s1² = 0.025, n2 = 4 with s2² = 0.02/3;
-- pooled variance (4*0.025 + 3*(0.02/3))/7 = 0.12/7.
example : pooledVariance 5 4 0.025 (0.02 / 3) = 0.12 / 7 := by
  have e1 : ((5 - 1 : ℕ) : ℝ) = 4 := by norm_num
  have e2 : ((4 - 1 : ℕ) : ℝ) = 3 := by norm_num
  have eD : ((5 + 4 - 2 : ℕ) : ℝ) = 7 := by norm_num
  unfold pooledVariance
  rw [e1, e2, eD]
  norm_num

-- Pooled-SD instance: the pooled SD is the square root of 0.12/7.
example : pooledStdDev 5 4 0.025 (0.02 / 3) = Real.sqrt (0.12 / 7) := by
  have e1 : ((5 - 1 : ℕ) : ℝ) = 4 := by norm_num
  have e2 : ((4 - 1 : ℕ) : ℝ) = 3 := by norm_num
  have eD : ((5 + 4 - 2 : ℕ) : ℝ) = 7 := by norm_num
  unfold pooledStdDev pooledVariance
  rw [e1, e2, eD]
  congr 1
  norm_num

-- Dixon Q instance: suspect 10.5, nearest 10.2, range 9.8-10.5;
-- Q = 0.3/0.7 = 3/7.
example : dixonQ 10.5 10.2 9.8 10.5 = 3 / 7 := by
  rw [dixonQ_of_ne 10.5 10.2 9.8 10.5 (by norm_num)]
  norm_num

-- Dixon procedure instance: Q = 3/7 rejects at qcrit = 0.41.
example : dixonReject (dixonQ 10.5 10.2 9.8 10.5) 0.41 := by
  have hQ : dixonQ 10.5 10.2 9.8 10.5 = 3 / 7 := by
    rw [dixonQ_of_ne 10.5 10.2 9.8 10.5 (by norm_num)]
    norm_num
  unfold dixonReject
  rw [hQ]
  norm_num

-- Dixon procedure instance: Q = 3/7 does not reject at qcrit = 0.56.
example : ¬ dixonReject (dixonQ 10.5 10.2 9.8 10.5) 0.56 := by
  have hQ : dixonQ 10.5 10.2 9.8 10.5 = 3 / 7 := by
    rw [dixonQ_of_ne 10.5 10.2 9.8 10.5 (by norm_num)]
    norm_num
  unfold dixonReject
  rw [hQ]
  norm_num

-- Grubbs instance: 10.5 against mean 10.0 with s = 0.2; G = 0.5/0.2 = 2.5.
example : grubbsG 10.5 10.0 0.2 = 2.5 := by
  rw [grubbsG_of_ne 10.5 10.0 0.2 (by norm_num)]
  norm_num

-- Grubbs procedure instance: G = 2.5 rejects at gcrit = 2.0.
example : grubbsReject (grubbsG 10.5 10.0 0.2) 2.0 := by
  have hG : grubbsG 10.5 10.0 0.2 = 2.5 := by
    rw [grubbsG_of_ne 10.5 10.0 0.2 (by norm_num)]
    norm_num
  unfold grubbsReject
  rw [hG]
  norm_num

-- LOD under the k = 3 convention: s = 0.02, m = 0.5 gives 0.12.
example : lodK3 0.02 0.5 = 0.12 := by
  unfold lodK3
  norm_num

-- LOD under the k = 3.3 convention: s = 0.02, m = 0.5 gives 0.132.
example : lodK33 0.02 0.5 = 0.132 := by
  unfold lodK33
  norm_num

-- t-interval duality instance: 10.1 lies within half-width 0.2 of 10.0
-- (half-width 0.8*0.5/√4 = 0.2).
example : (10.1 : ℝ) ∈ tInterval 10.0 0.5 4 0.8 := by
  have hsqrt : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [mem_tInterval_iff]
  unfold tHalfWidth
  rw [hsqrt]
  norm_num

-- Boundary: n = 1 gives no t-procedure claim (variance degenerates to 0).
example (x : Fin 1 → ℝ) : sampleVariance x = 0 := sampleVariance_fin_one x

-- Boundary: hypotheses needing 2 ≤ n are vacuous at n = 1.
example : ¬ (2 ≤ 1) := by decide

-- Boundary: degenerate (non-normal) zero-spread input gives no Grubbs claim.
example (xj xbar : ℝ) : grubbsG xj xbar 0 = 0 := grubbsG_of_sd_zero xj xbar

-- Boundary: no-spread input gives Q = 0, hence no Dixon rejection.
example (s r m : ℝ) : dixonQ s r m m = 0 := dixonQ_of_no_spread s r m m rfl

-- Boundary: constant samples have zero SD, so Grubbs reports 0 end to end.
example (c : ℝ) (x : Fin 5 → ℝ) (h : ∀ i, x i = c) (j : Fin 5) :
    grubbsG (x j) (sampleMean x) (sampleStdDev x) = 0 := by
  rw [sampleStdDev_const 5 (by norm_num) c x h]
  exact grubbsG_of_sd_zero _ _

end

end Chemistry.StatisticalTreatmentTest
