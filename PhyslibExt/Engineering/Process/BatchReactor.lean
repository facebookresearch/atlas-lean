/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Batch first-order reaction: consumed concentration bounds

## i. Overview

Closed, constant-volume batch reaction with first-order decay and the
explicit solution `c(t) = c0 * exp (-k * t)` used by
`EarthScience.firstOrder_decay_hasDerivAt` in
`PhyslibExt/EarthScience/FirstOrderKinetics.lean`. This module records the
amount/concentration bookkeeping of that solution: how much has been
consumed, and in which range it lies. It reproves no IVP; the explicit
formula is the solution.

## ii. Key results

- `BatchReactor.firstOrder_consumed_mem_Icc`: for `k, c0, t ≥ 0`, the
  consumed concentration `c0 - c(t)` lies in `Set.Icc 0 c0`.
- `BatchReactor.consumed_amount_mem_Icc`: the amount form at constant
  volume `V > 0`.
- `BatchReactor.consumed_pos`: strict consumption in the interior regime.

## iii. Table of contents

- A. Consumed concentration and its range

## iv. References

- `PhyslibExt/EarthScience/FirstOrderKinetics.lean`: the exponential
  profile, its derivative and its integrated consumption identity.
- R. M. Felder, R. W. Rousseau and L. G. Bullard, *Elementary Principles
  of Chemical Processes*, 4th ed., Wiley (2016), Chapter 4.
-/

@[expose] public section

namespace Engineering.Process.BatchReactor

/-- Concentration consumed by time `t` in a closed constant-volume
first-order batch reaction with initial concentration `c0` and rate
constant `k`: `c0 - c(t)` for the explicit solution
`c(t) = c0 * exp (-k * t)`. -/
noncomputable def consumed (k c0 t : ℝ) : ℝ :=
  c0 - c0 * Real.exp (-k * t)

/-- Remaining concentration at time `t`: `c0 * exp (-k * t)`. -/
lemma remaining_nonneg {k c0 t : ℝ} (hc0 : 0 ≤ c0) :
    0 ≤ c0 * Real.exp (-k * t) := by
  exact mul_nonneg hc0 (Real.exp_nonneg _)

/-- At time zero nothing is consumed. -/
lemma consumed_zero (k c0 : ℝ) : consumed k c0 0 = 0 := by
  simp [consumed]

/-- With no reactant, nothing is consumed. -/
lemma consumed_of_c0_eq_zero (k t : ℝ) : consumed k 0 t = 0 := by
  simp [consumed]

/-- With rate constant zero, nothing is consumed. -/
lemma consumed_of_k_eq_zero (c0 t : ℝ) : consumed 0 c0 t = 0 := by
  simp [consumed]

/-- **Consumption bound.** For `k ≥ 0`, `c0 ≥ 0` and `t ≥ 0`, the consumed
concentration lies between `0` and the initial concentration:
`0 ≤ consumed ≤ c0`. -/
lemma firstOrder_consumed_mem_Icc {k c0 t : ℝ} (hk : 0 ≤ k) (hc0 : 0 ≤ c0)
    (ht : 0 ≤ t) : consumed k c0 t ∈ Set.Icc 0 c0 := by
  have hkt : -k * t ≤ 0 := by
    have h : 0 ≤ k * t := mul_nonneg hk ht
    linarith
  have hexp : Real.exp (-k * t) ≤ 1 := Real.exp_le_one_iff.mpr hkt
  have hrem : 0 ≤ c0 * Real.exp (-k * t) := mul_nonneg hc0 (Real.exp_nonneg _)
  have hle : c0 * Real.exp (-k * t) ≤ c0 := by
    calc c0 * Real.exp (-k * t) ≤ c0 * 1 := mul_le_mul_of_nonneg_left hexp hc0
      _ = c0 := mul_one c0
  rw [Set.mem_Icc]
  unfold consumed
  constructor <;> linarith

/-- Amount form at constant volume `V > 0`: the consumed amount
`V * consumed` lies between `0` and the initial amount `V * c0`. -/
lemma consumed_amount_mem_Icc {k c0 t V : ℝ} (hk : 0 ≤ k) (hc0 : 0 ≤ c0)
    (ht : 0 ≤ t) (hV : 0 < V) :
    V * consumed k c0 t ∈ Set.Icc 0 (V * c0) := by
  have h := firstOrder_consumed_mem_Icc hk hc0 ht
  rw [Set.mem_Icc] at h ⊢
  constructor
  · exact mul_nonneg hV.le h.1
  · exact mul_le_mul_of_nonneg_left h.2 hV.le

/-- Strict consumption in the interior regime `k > 0`, `c0 > 0`, `t > 0`. -/
lemma consumed_pos {k c0 t : ℝ} (hk : 0 < k) (hc0 : 0 < c0) (ht : 0 < t) :
    0 < consumed k c0 t := by
  have hkt : -k * t < 0 := by
    have h : 0 < k * t := mul_pos hk ht
    linarith
  have hexp : Real.exp (-k * t) < 1 := Real.exp_lt_one_iff.mpr hkt
  have hlt : c0 * Real.exp (-k * t) < c0 * 1 := mul_lt_mul_of_pos_left hexp hc0
  unfold consumed
  linarith

end Engineering.Process.BatchReactor
