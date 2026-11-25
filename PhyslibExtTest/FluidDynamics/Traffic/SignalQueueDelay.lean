/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.SignalQueueDelay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Cycle-average signal delay checks

Concrete consumers of `PhyslibExt.FluidDynamics.Traffic.SignalQueueDelay`: the sample cycle
`lam = 1`, `mu = 3`, `R = G = 2` with arrival-average delay `3 / 4`, normalized queue area
`3 / 4` and arrival-weighted delay `3`; zero mean delay at `R = 0`; the zero-delay value at
`s = 0`; falsity of the conclusions at `lam = 0`; rejection of capacity equality
`(1, 3, 2, 1)` and of `G = 0`, with the non-strict-capacity degeneracy at `R = G = 0`;
redundancy consequences of strict capacity; the `mu = -1` backlog control; and necessity of
`0 ≤ R` and of the positive arrival rate.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

None; every declaration is a check against `PhyslibExt.FluidDynamics.Traffic.SignalQueueDelay`.

## iii. Table of contents

- A. Sample cycle and pointwise value
- B. Premise and capacity controls

## iv. References

- J.-Y. Le Boudec and P. Thiran, *Network Calculus*, LNCS 2050, Section 1.1.

-/

open scoped NNReal ENNReal
open MeasureTheory Cslib.Algorithms.Networking.NetworkCalculus

namespace PhyslibExtTest.FluidDynamics.Traffic.SignalQueueDelay

open FluidDynamics.Traffic.SignalQueue

/-! ## A. Sample cycle and pointwise value -/

-- W1 premises at the sample (1, 3, 2, 2) and the five conclusions
example : 0 < (1 : ℝ) * (2 + 2) := arrivalVolume_pos (mu := 3) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
example : (∫ t in (0 : ℝ)..(2 + 2), queueLen 1 3 2 t) / (1 * (2 + 2)) = 3 / 4 := by
  rw [queueArea_div_arrivalVolume (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num
example : (∫⁻ s in Set.Ico 0 ((2 : ℝ) + 2), delay (arrivals 1) (departures 1 3 2) s.toNNReal
    ∂(ENNReal.ofReal 1 • volume)) / ENNReal.ofReal (1 * (2 + 2)) = ENNReal.ofReal (3 / 4) := by
  rw [arrivalAverage_delay (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num
example : ∫⁻ s in Set.Ico 0 ((2 : ℝ) + 2), delay (arrivals 1) (departures 1 3 2) s.toNNReal
    ∂(ENNReal.ofReal 1 • volume) = ENNReal.ofReal 3 := by
  rw [arrivalWeighted_delay_eq_queueArea (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), queueLen_integral_cycle (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num
-- R = 0: zero mean delay
example : (∫⁻ s in Set.Ico 0 ((0 : ℝ) + 2), delay (arrivals 1) (departures 1 3 0) s.toNNReal
    ∂(ENNReal.ofReal 1 • volume)) / ENNReal.ofReal (1 * (0 + 2)) = 0 := by
  rw [arrivalAverage_delay (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num


-- W2 pointwise values at the sample: the delay at `s = 0` is `0`; the queue is nonempty in
-- the red branch at `s = 1` (one vehicle waiting, none departed), and empty at the clearance
-- time `s = 3` and after it (`s = 4`), where the delay is again `0`.
example : delay (arrivals 1) (departures 1 3 2) 0 = 0 := by
  refine le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, by simp [arrivals]⟩ (by simp)
example : departures 1 3 2 1 = 0 ∧ backlog (arrivals 1) (departures 1 3 2) 1 = 1 := by
  have hd : departures 1 3 2 1 = 0 := by norm_num [departures, queueLen]
  refine ⟨hd, ?_⟩
  have ha : arrivals 1 1 = 1 := by simp [arrivals]
  simp only [backlog, ha, hd, ENNReal.coe_zero, tsub_zero, ENNReal.coe_one]
example : delay (arrivals 1) (departures 1 3 2) 3 = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le ⟨0, ?_⟩ (by simp)
  have ha : arrivals 1 3 = 3 := by simp [arrivals]
  have hd : departures 1 3 2 (3 + 0) = 3 := by norm_num [departures, queueLen]
  rw [ha, hd]
example : delay (arrivals 1) (departures 1 3 2) 4 = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le ⟨0, ?_⟩ (by simp)
  have ha : arrivals 1 4 = 4 := by simp [arrivals]
  have hd : departures 1 3 2 (4 + 0) = 4 := by norm_num [departures, queueLen]
  rw [ha, hd]

/-! ## B. Premise and capacity controls -/

-- C1 lam = 0: the T1 conclusion, the T2 conclusion and the T5 conclusion are all false
example : ¬ (0 < (0 : ℝ) * (2 + 2)) := by norm_num
example : (∫ t in (0 : ℝ)..(2 + 2), queueLen 0 3 2 t) / (0 * (2 + 2))
    ≠ 2 ^ 2 * 3 / (2 * (3 - 0) * (2 + 2)) := by norm_num
example : (∫⁻ s in Set.Ico 0 ((2 : ℝ) + 2), delay (arrivals 0) (departures 0 3 2) s.toNNReal
    ∂(ENNReal.ofReal 0 • volume)) / ENNReal.ofReal (0 * (2 + 2))
    ≠ ENNReal.ofReal (2 ^ 2 * 3 / (2 * (3 - 0) * (2 + 2))) := by
  simp

-- C2 capacity: strict capacity fails at equality (1, 3, 2, 1) and at G = 0
example : ¬ ((1 : ℝ) * (2 + 1) < 3 * 1) := by norm_num
example (lam mu R : ℝ) (hlam : 0 < lam) (hR : 0 ≤ R) : ¬ (lam * (R + 0) < mu * 0) := by
  simp only [add_zero, mul_zero, not_lt]; exact mul_nonneg hlam.le hR
-- non-strict capacity would admit R = G = 0, where the T1 conclusion is false
example : (1 : ℝ) * (0 + 0) ≤ 3 * 0 ∧ ¬ (0 < (1 : ℝ) * (0 + 0)) := by norm_num

-- C3 premise redundancy: strict capacity with 0 ≤ G gives lam < mu; with lam < mu it gives 0 < G
example (lam mu R G : ℝ) (hlam : 0 < lam) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) : lam < mu := by
  by_contra h; have h' := not_lt.mp h
  nlinarith [mul_nonneg hlam.le hR, mul_le_mul_of_nonneg_right h' hG]
example (lam mu R G : ℝ) (hlam : 0 < lam) (hmu : lam < mu) (hR : 0 ≤ R)
    (hcap : lam * (R + G) < mu * G) : 0 < G := by
  by_contra h; have h' := not_lt.mp h
  nlinarith [mul_nonneg hlam.le hR, mul_le_mul_of_nonpos_right hmu.le h']

-- C4 T3 needs mu ≥ 0 (here mu = -1): backlog 3, queue length 4 at s = 3
example : backlog (arrivals 1) (departures 1 (-1) 2) 3 ≠ ENNReal.ofReal (queueLen 1 (-1) 2 3) := by
  have h1 : arrivals 1 3 = 3 := by simp [arrivals]
  have h2 : departures 1 (-1) 2 3 = 0 := by norm_num [departures, queueLen]
  have hq : queueLen 1 (-1) 2 (3 : ℝ) = 4 := by norm_num [queueLen]
  simp only [backlog, h1, h2, hq, ENNReal.coe_zero, tsub_zero]
  norm_num


-- C6 hR is necessary in T2 (and T5): R = -1, G = 2, lam = 1, mu = 3 satisfies the other premises,
-- the queue is identically 0 on [0, 1], the left side is 0 and the closed form is 3/4.
example : (1 : ℝ) * (-1 + 2) < 3 * 2 ∧
    (∫ t in (0 : ℝ)..(-1 + 2), queueLen 1 3 (-1) t) / (1 * (-1 + 2))
      ≠ (-1) ^ 2 * 3 / (2 * (3 - 1) * (-1 + 2)) := by
  have hq : ∀ t ∈ Set.uIcc (0 : ℝ) (-1 + 2), queueLen 1 3 (-1) t = 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have h1 : ¬ t ≤ -1 := by linarith [ht.1]
    simp only [queueLen, h1, ↓reduceIte]
    exact max_eq_left (by nlinarith [ht.1])
  refine ⟨by norm_num, ?_⟩
  rw [intervalIntegral.integral_congr hq]
  norm_num

-- C7 hlam is a domain premise in T4: at lam = 0 both sides of the T4 conclusion are 0
example : ∫⁻ s in Set.Ico 0 ((2 : ℝ) + 2), delay (arrivals 0) (departures 0 3 2) s.toNNReal
    ∂(ENNReal.ofReal 0 • volume) = ENNReal.ofReal (∫ t in (0 : ℝ)..(2 + 2), queueLen 0 3 2 t) := by
  have hq : queueLen 0 3 2 = fun _ => 0 := by
    funext t
    unfold queueLen
    split_ifs with h
    · ring
    · exact max_eq_left (by nlinarith)
  simp [hq]

end PhyslibExtTest.FluidDynamics.Traffic.SignalQueueDelay

#print axioms FluidDynamics.Traffic.SignalQueue.arrivalVolume_pos
#print axioms FluidDynamics.Traffic.SignalQueue.queueArea_div_arrivalVolume
#print axioms FluidDynamics.Traffic.SignalQueue.isFlowPair_and_backlog_eq_queueLen
#print axioms FluidDynamics.Traffic.SignalQueue.arrivalWeighted_delay_eq_queueArea
#print axioms FluidDynamics.Traffic.SignalQueue.arrivalAverage_delay
