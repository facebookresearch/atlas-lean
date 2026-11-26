/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ThermalBalances.FreezingTime
import Mathlib.Tactic.NormNum

open MeasureTheory
open Domains.Chemistry.ThermalBalances.FreezingTime

-- Both sensible heat terms contribute, and this constant rate equals the cap.
example : 0 < (8 : ℝ) ∧ (8 : ℝ) / 4 ≤ 2 := by
  have h := freezing_time_lower_bound 2 3 2 1 1 1 2 4 2 (fun _ => 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    intervalIntegrable_const (fun _ _ => ⟨by norm_num, le_rfl⟩)
    (by rw [intervalIntegral.integral_const]; norm_num [smul_eq_mul])
  simpa only [show (2 : ℝ) * (1 * (3 - 2) + 2 + 1 * (2 - 1)) = 8 by norm_num] using h

-- Only the latent term contributes, and the rate is strictly below its cap.
example : 0 < (2 : ℝ) ∧ (2 : ℝ) / 3 ≤ 2 := by
  have h := freezing_time_lower_bound 1 0 0 0 1 1 2 3 2 (fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl le_rfl (by norm_num) (by norm_num)
    intervalIntegrable_const (fun _ _ => ⟨by norm_num, by norm_num⟩)
    (by rw [intervalIntegral.integral_const]; norm_num [smul_eq_mul])
  simpa only [show (1 : ℝ) * (1 * (0 - 0) + 2 + 1 * (0 - 0)) = 2 by norm_num] using h
