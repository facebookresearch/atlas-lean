/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.AlgebraicCoefficientBound

@[expose] public section

-- exactSource consumer: the original binders apply verbatim.
private theorem exactSource (φ : PowerSeries ℂ) (hφ : IsAlgebraic (Polynomial ℂ) φ) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n φ‖ ≤ C * R ^ n :=
  PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex φ hφ

-- The zero series is algebraic, and the bound it receives is usable
-- coefficient by coefficient.
example : ∃ C R : ℝ, ∀ n : ℕ,
    ‖PowerSeries.coeff n (0 : PowerSeries ℂ)‖ ≤ C * R ^ n :=
  exactSource 0 ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩

-- A concrete coefficient bound extracted from the existential.
example : ∃ C R : ℝ, ‖PowerSeries.coeff 3 (0 : PowerSeries ℂ)‖ ≤ C * R ^ 3 := by
  obtain ⟨C, R, h⟩ := exactSource 0 ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩
  exact ⟨C, R, h 3⟩
