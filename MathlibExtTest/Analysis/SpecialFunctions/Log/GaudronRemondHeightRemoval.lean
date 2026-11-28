/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.GaudronRemondHeightRemoval

open Real GaudronRemond

-- Lemme 9.4 in its general form.
example (g : ℕ) (hg : 1 ≤ g) {D h M : ℝ} (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hMQ : M ≤ max (h + log ((9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3)) / 2)
      1) :
    (9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3) ≤
      ((14 * g : ℝ) ^ (64 * g ^ 2) * D * max h (max (log D) 1) ^ 2) ^ (2 ^ 10 * g ^ 3) :=
  pow_mul_boundP_pow_le g hg hD hM hMQ

-- The definition of `P` unfolds to the formula of p. 2098.
example (g : ℕ) (D M : ℝ) :
    boundP g D M = 4 * (9 * g : ℝ) ^ (4 * g) * (8 * g : ℝ) ^ (64 * g ^ 2) * D *
      max (M + 3 / 2 * g) (log (4 * (9 * g : ℝ) ^ (4 * g) * D)) ^ 2 :=
  rfl

-- The case `M = 1` needs no hypothesis on `h`: the maximum in Raynaud's estimate is `≥ 1`.
example (g : ℕ) (hg : 1 ≤ g) {D h : ℝ} (hD : 1 ≤ D) :
    (9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D 1 ^ (2 ^ 10 * g ^ 3) ≤
      ((14 * g : ℝ) ^ (64 * g ^ 2) * D * max h (max (log D) 1) ^ 2) ^ (2 ^ 10 * g ^ 3) :=
  pow_mul_boundP_pow_le g hg hD le_rfl (le_max_right _ _)

-- Elliptic curves over `ℚ` (`g = 1`, `D = 1`): with `κ = (14 ^ 64 · max(h, 1)^2)^1024`, the
-- bound applies to any `M ≥ 1` with `M ≤ max(h + ½ log Q, 1)`.
example {h M : ℝ} (hM : 1 ≤ M)
    (hMQ : M ≤ max (h + log ((9 * 1 : ℝ) ^ 96 * boundP 1 1 M ^ 1024) / 2) 1) :
    (9 * 1 : ℝ) ^ 96 * boundP 1 1 M ^ 1024 ≤ ((14 : ℝ) ^ 64 * max h 1 ^ 2) ^ 1024 := by
  have := pow_mul_boundP_pow_le 1 le_rfl le_rfl hM (h := h) (by simpa using hMQ)
  simpa using this
