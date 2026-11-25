/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DiophantineApproximation.DistRoundPowFourierExpansion

open Filter

-- The mean value: for `k = 2` the zeroth Fourier coefficient is `1 / 12`.
example : (∫ u in (0 : ℝ)..1, ((|u - round u| ^ 2 : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) * (u : ℂ)))) = (1 / 12 : ℂ) := by
  have h0 := (MetaMathlibExt.dist_round_pow_fourier_expansion 2 (by norm_num)).1
  have hreal : (1 : ℝ) / (2 ^ 2 * (((2 : ℕ) : ℝ) + 1)) = 1 / 12 := by norm_num
  have hval : ((1 / (2 ^ 2 * (((2 : ℕ) : ℝ) + 1)) : ℝ) : ℂ) = (1 / 12 : ℂ) := by
    rw [hreal]
    norm_num
  rw [hval] at h0
  exact h0

-- The coefficient bound is available with the statement exactly as written.
example : (let g : ℝ → ℝ := fun u => |u - round u| ^ 1
    let c : ℤ → ℂ := fun m => ∫ u in (0 : ℝ)..1,
      (g u : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
    ∃ C : ℝ, ∀ m : ℤ, m ≠ 0 → ‖c m‖ ≤ C / (m : ℝ) ^ 2) :=
  (MetaMathlibExt.dist_round_pow_fourier_expansion 1 (by norm_num)).2.1
