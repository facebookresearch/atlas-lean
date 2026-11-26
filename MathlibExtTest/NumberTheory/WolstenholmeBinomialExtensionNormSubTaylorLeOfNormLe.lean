/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeOfNormLe
import Mathlib.Tactic.Positivity

/-! # Tests for the higher `p`-adic mean value theorem -/

namespace MathlibExtTest.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeOfNormLe

open MetaMathlibExt

-- At `h = 0` the Taylor remainder vanishes: the bound is `‖0‖ * C = 0`.
example (N : ℕ) (a : ℕ → ℚ_[2]) (t : ℚ_[2]) (C : ℝ) (ht : ‖t‖ ≤ 1)
    (hC₀ : 0 ≤ C) (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial 1 • a j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, (t + 0) ^ j • a j -
        ∑ q ∈ Finset.range 1, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[2]) * t ^ (j - q) * (0 : ℚ_[2]) ^ q) • a j‖ = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := norm_sub_taylor_le_of_norm_le (p := 2) (B := ℚ_[2]) N 1 a t 0 C ht le_rfl
    (by decide) (fun _ => by rw [norm_zero]; positivity)
    (fun hcon => absurd hcon (by decide)) hC₀ hC
  have hRHS : ‖(0 : ℚ_[2]) ^ 1 / ((1 : ℕ) : ℚ_[2])‖ * C = 0 := by simp
  rw [hRHS] at h
  exact le_antisymm h (norm_nonneg _)

-- With all coefficients zero, the bound forces the Taylor difference to vanish.
example (N : ℕ) (t h : ℚ_[2]) (ht : ‖t‖ ≤ 1)
    (hh : ‖h‖ ≤ (2 : ℝ) ^ (-(1 / ((2 : ℝ) - ((1 : ℕ) : ℝ))))) :
    ‖∑ j ∈ Finset.range N, (t + h) ^ j • (0 : ℚ_[2]) -
        ∑ q ∈ Finset.range 1, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[2]) * t ^ (j - q) * h ^ q) • (0 : ℚ_[2])‖ = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := norm_sub_taylor_le_of_norm_le (p := 2) (B := ℚ_[2]) N 1 (fun _ => 0) t h 0 ht
    le_rfl (by decide) (fun _ => hh) (fun hcon => absurd hcon (by decide)) le_rfl
    (fun j _ => by simp)
  rw [mul_zero] at h
  exact le_antisymm h (norm_nonneg _)

end MathlibExtTest.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeOfNormLe
