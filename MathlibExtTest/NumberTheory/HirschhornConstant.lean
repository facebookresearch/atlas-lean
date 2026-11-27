/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HirschhornConstant

open Filter Topology MetaMathlibExt

-- Express the limit using the factorial product constant in place of its closed form.
example :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 12) *
        ∏ k ∈ Finset.Icc 1 n, ((k.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k)))
      atTop (𝓝 (factorialProductConstant 1)) := by
  obtain ⟨h, h₁⟩ := tendsto_hirschhorn_constant
  rwa [h₁] at h

-- At n = 1 the normalized product consists of e / √(2π).
example :
    (1 : ℝ) ^ (-(1 : ℝ) / 12) *
        (∏ k ∈ Finset.Icc 1 (1 : ℕ), ((k.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k))) =
      Real.exp 1 / Real.sqrt (2 * Real.pi) := by
  simp [div_eq_mul_inv]
