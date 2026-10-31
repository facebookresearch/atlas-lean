/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.CompletedLFunctionGrowth

/-!
# Tests for the factorial-type growth of completed `L`-functions
-/

@[expose] public section

open Filter Bornology

namespace CompletedLFunctionGrowthTest

/-- The completed Riemann zeta function `Λ₀` is of factorial type, hence of order at most `1`. -/
example : ∀ᶠ s in cobounded ℂ, ‖completedRiemannZeta₀ s‖ ≤ ‖s‖ ^ (4 * ‖s‖) := by
  obtain ⟨A, B, -, hB, h⟩ := HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_mul_pow_mul_factorial 0
  refine eventually_norm_le_rpow_of_le_mul_pow_mul_factorial (by linarith) (A := A) ?_
  intro s N hN
  simpa [completedRiemannZeta₀] using h s N hN

/-- The zero function on `ZMod 3` trivially has factorial type. -/
example : ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (M : ℕ),
    ‖s‖ + 1 ≤ M → ‖ZMod.completedLFunction₀ (0 : ZMod 3 → ℂ) s‖ ≤ A * B ^ M * M.factorial :=
  ZMod.exists_norm_completedLFunction₀_le_mul_pow_mul_factorial 0

end CompletedLFunctionGrowthTest
