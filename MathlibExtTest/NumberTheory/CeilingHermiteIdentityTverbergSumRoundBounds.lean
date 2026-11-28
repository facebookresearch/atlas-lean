/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds` -/

namespace MathlibExtTest.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds

open MetaMathlibExt

-- In two dimensions the bounds say the sum lies in `[-1, 1]`.
example : -1 ≤ tverbergSum round ![1, 1] 2 0 ∧ tverbergSum round ![1, 1] 2 0 ≤ 1 := by
  have h := (tverbergSum_round_bounds (ℓ := 2) (by decide)).1 ![1, 1] 2 0
  simpa using h

-- Sharpness at `ℓ = 2` and `r = 1`: both bounds are attained.
example : tverbergSum round (fun _ : Fin 2 => (1 : ℤ)) (2 * 1) 0 = -1 := by
  have h := (tverbergSum_round_bounds (ℓ := 2) (by decide)).2 1 (by decide)
  norm_num at h ⊢
  exact h.1

example : tverbergSum round (fun _ : Fin 2 => (1 : ℤ)) (2 * 1) 1 = 1 := by
  have h := (tverbergSum_round_bounds (ℓ := 2) (by decide)).2 1 (by decide)
  norm_num at h ⊢
  exact h.2

-- Sharpness at `ℓ = 3` and `r = 2`.
example : tverbergSum round (fun _ : Fin 3 => (2 : ℤ)) (2 * 2) 0 = 2 := by
  have h := (tverbergSum_round_bounds (ℓ := 3) (by decide)).2 2 (by decide)
  norm_num at h ⊢
  exact h.1

-- The two-sided bound as an absolute-value estimate.
example {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) :
    |tverbergSum round a m k| ≤ 2 ^ (ℓ - 2) := by
  have h := (tverbergSum_round_bounds hℓ).1 a m k
  exact abs_le.mpr h

end MathlibExtTest.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds
