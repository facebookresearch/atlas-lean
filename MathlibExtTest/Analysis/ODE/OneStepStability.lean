/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.OneStepStability

/-! # Tests for `MathlibExt.Analysis.ODE.OneStepStability` -/

namespace MathlibExtTest.OneStepStability

open MathlibExt.Analysis.ODE.OneStepMethod Finset Real

-- Test section: explicit Euler for `x' = -x` is stable on `[0, 1]`, since `Φ(t, x, h) = -x` is
-- `1`-Lipschitz in the state.
example : IsStable (fun (_ : ℝ) (x : ℝ) (_ : ℝ) ↦ -x) 0 1 :=
  isStable_of_lipschitz zero_le_one fun _ _ _ _ a b ↦ by
    rw [one_mul, show -a - -b = -(a - b) by ring, norm_neg]

-- Test section: a zero increment is stable with any `L ≥ 0`, here `L = 0`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t₀ T : ℝ) :
    IsStable (fun (_ : ℝ) (_ : E) (_ : ℝ) ↦ (0 : E)) t₀ T :=
  isStable_of_lipschitz le_rfl fun _ _ _ _ a b ↦ by simp

-- Test section: the explicit error bound on one step of explicit Euler for `x' = x` with
-- step `1/2`: from `x 0 = 1`, `z 0 = 1` and perturbation `δ 1 = 1`, the gap after one step is at
-- most `e^{1/2 - 1/2} * 1 = 1`.
example (x z : ℕ → ℝ) (hx0 : x 0 = 1) (hz0 : z 0 = 1)
    (hx : x 1 = x 0 + (1 / 2 - 0 : ℝ) • x 0) (hz : z 1 = z 0 + (1 / 2 - 0 : ℝ) • z 0 + 1) :
    ‖x 1 - z 1‖ ≤ 1 := by
  have h := norm_sub_le (Φ := fun (_ : ℝ) (y : ℝ) (_ : ℝ) ↦ y) (L := 1) (J := 1)
    (t := fun j ↦ (j : ℝ) / 2) (x := x) (z := z) (δ := fun _ ↦ 1)
    (fun j hj ↦ by norm_num [Nat.lt_one_iff.1 hj])
    (fun _ _ a b ↦ by simp)
    (fun j hj ↦ by obtain rfl := Nat.lt_one_iff.1 hj; show x 1 = _; rw [hx]; norm_num)
    (fun j hj ↦ by obtain rfl := Nat.lt_one_iff.1 hj; show z 1 = _; rw [hz]; norm_num)
    1 le_rfl
  norm_num [hx0, hz0] at h
  exact h

end MathlibExtTest.OneStepStability
