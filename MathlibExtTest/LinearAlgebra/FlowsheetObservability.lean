/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.FlowsheetObservability

/-! # Observability on a fiber with an unmeasured coordinate -/

open MathlibExt.LinearAlgebra

private abbrev first : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ
private abbrev second : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
private abbrev balance : ℝ × ℝ →ₗ[ℝ] ℝ := 0
private abbrev readings := balance.prod first

-- The first coordinate is determined on every fiber, but the second can vary.
example (x₀ : ℝ × ℝ) : (∀ x, readings x = readings x₀ → x.1 = x₀.1) ∧
    ¬ (∀ x, readings x = readings x₀ → x.2 = x₀.2) := by
  constructor
  · apply (flowsheet_observability balance first first (x₀ := x₀) rfl).2.mpr
    intro v hv
    exact LinearMap.mem_ker.mpr (congrArg Prod.snd (LinearMap.mem_ker.mp hv))
  · intro h
    have hk := (flowsheet_observability balance first second (x₀ := x₀) rfl).2.mp h
    have hv : (0, 1) ∈ LinearMap.ker readings := by
      simp [LinearMap.mem_ker, balance, first]
    have h1 : (1 : ℝ) = 0 := LinearMap.mem_ker.mp (hk hv)
    exact one_ne_zero h1
