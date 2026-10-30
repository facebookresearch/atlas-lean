/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.OneArm
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.OneArm`

* `roa_eps` at `c = 1/2` is `1` (since `1 - 1/2 = 2⁻¹`); `roa_eps_pos`.
* `roa_one_arm_polynomial` and `roa_one_arm_tendsto_zero` for the extremal sequence
  `a n = (1/2)^⌊log₂ n⌋`.
-/

@[expose] public section

open StatMech.RSW.OneArm

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.OneArm

example : roa_eps (1 / 2) = 1 := by
  unfold roa_eps
  rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg,
    div_self (Real.log_pos (by norm_num)).ne']

example : 0 < roa_eps (1 / 3) := roa_eps_pos (by norm_num) (by norm_num)

/-- The extremal sequence `(1/2)^⌊log₂ n⌋`. -/
noncomputable def a (n : ℕ) : ℝ := (1 - 1 / 2) ^ Nat.log 2 n

example : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → a n ≤ C * (n : ℝ) ^ (-ε) :=
  roa_one_arm_polynomial a (by norm_num) (by norm_num) (fun _ _ => le_rfl)

example : Filter.Tendsto a Filter.atTop (nhds 0) :=
  roa_one_arm_tendsto_zero a (by norm_num) (by norm_num) (fun _ => by unfold a; positivity)
    (fun _ _ => le_rfl)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.OneArm
