/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Welfare.LinearDeadweightLoss

/-!
# Tests for the linear deadweight loss

`Pd q = 10 - q`, `Ps q = q`: loss `τ² / 4` for every `τ`, so the Harberger remainder vanishes;
`Pd q = 12 - 2 q`, `Ps q = 3 + q`, `τ = 3`: `q* = 3`, `q_τ = 2`, loss `3 / 2`, the triangle form
`3 · (3 - 2) / 2`, the tax equilibrium, and the interior-regime bounds.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Welfare.LinearDeadweightLoss

open MathlibExt.Economics.DeadweightLoss

example (τ : ℝ) :
    deadweightLoss (fun q => 10 - 1 * q) (fun q => 0 + 1 * q) ((10 - 0) / (1 + 1))
      ((10 - 0 - τ) / (1 + 1)) = τ ^ 2 / 4 := by
  have h := deadweightLoss_linear (α := 10) (β := 1) (γ := 0) (δ := 1) (τ := τ)
    (by norm_num)
  exact h.2.trans (by norm_num)

example : ((12 - 3 : ℝ) / (2 + 1)) = 3 := by norm_num

example : ((12 - 3 - 3 : ℝ) / (2 + 1)) = 2 := by norm_num

example :
    deadweightLoss (fun q => 12 - 2 * q) (fun q => 3 + 1 * q) ((12 - 3) / (2 + 1))
      ((12 - 3 - 3) / (2 + 1)) = 3 / 2 := by
  have h := deadweightLoss_linear (α := 12) (β := 2) (γ := 3) (δ := 1) (τ := 3)
    (by norm_num)
  exact h.2.trans (by norm_num)

example (τ : ℝ) :
    deadweightLoss (fun q => 10 - 1 * q) (fun q => 0 + 1 * q) ((10 - 0) / (1 + 1))
        ((10 - 0 - τ) / (1 + 1)) - τ ^ 2 / (2 * 2) = 0 := by
  have h := deadweightLoss_linear (α := 10) (β := 1) (γ := 0) (δ := 1) (τ := τ)
    (by norm_num)
  rw [h.2]
  field_simp
  ring

example : IsTaxEquilibrium (fun q => 12 - 2 * q) (fun q => 3 + 1 * q) 3
    ((12 - 3 - 3) / (2 + 1)) := by
  exact isTaxEquilibrium_linear (α := 12) (β := 2) (γ := 3) (δ := 1) (τ := 3)
    (by norm_num)

example :
    deadweightLoss (fun q => 12 - 2 * q) (fun q => 3 + 1 * q) ((12 - 3) / (2 + 1))
      ((12 - 3 - 3) / (2 + 1)) = 3 * (3 - 2) / 2 := by
  have h := deadweightLoss_linear (α := 12) (β := 2) (γ := 3) (δ := 1) (τ := 3)
    (by norm_num)
  exact h.1.trans (by norm_num)

example :
    0 ≤ (12 - 3 - 3 : ℝ) / (2 + 1) ∧ (12 - 3 - 3 : ℝ) / (2 + 1) ≤ (12 - 3) / (2 + 1) ∧
      0 ≤ deadweightLoss (fun q => 12 - 2 * q) (fun q => 3 + 1 * q) ((12 - 3) / (2 + 1))
        ((12 - 3 - 3) / (2 + 1)) := by
  exact linear_interior_regime (α := 12) (β := 2) (γ := 3) (δ := 1) (τ := 3)
    (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Economics.Welfare.LinearDeadweightLoss
