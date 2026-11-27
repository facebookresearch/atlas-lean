/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.BanachAlaogluBourbaki
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Tests for the Banach–Alaoglu–Bourbaki theorem

Test a closed cylinder in a countable product of real lines, including the
coordinate functional that attains the polar bound and one that exceeds it.
-/

open MathlibExt.Analysis.BanachAlaogluWanted.Analysis
open Set Topology

local notation "U" => (fun x : ℕ → ℝ ↦ x 0) ⁻¹' Metric.closedBall (0 : ℝ) 1

example : IsCompact (weakStarPolar (ℕ → ℝ) U) :=
  banach_alaoglu_bourbaki _ _ <|
    (continuous_apply 0).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ zero_lt_one)

example : (ContinuousLinearMap.proj 0 : WeakDual ℝ (ℕ → ℝ)) ∈ weakStarPolar _ U :=
  fun _ hx ↦ mem_closedBall_zero_iff.mp hx

example : (ContinuousLinearMap.proj 1 : WeakDual ℝ (ℕ → ℝ)) ∉ weakStarPolar _ U := by
  intro h
  have hx : Pi.single 1 (2 : ℝ) ∈ U := by simp
  have hle' := h _ hx
  change ‖(Pi.single 1 (2 : ℝ) : ℕ → ℝ) 1‖ ≤ 1 at hle'
  have hle : ‖(2 : ℝ)‖ ≤ 1 := by
    simpa only [Pi.single_eq_same] using hle'
  norm_num at hle
