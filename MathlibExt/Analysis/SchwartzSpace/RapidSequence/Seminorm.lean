/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SchwartzSpace.RapidSequence
public import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Monotonicity of the rapid-sequence seminorms

The positive weights `(n + 1) ^ k` increase with the exponent. Hence the weighted
supremum seminorms form an increasing family on the space of rapidly decreasing
sequences. A bound for a larger exponent also bounds every smaller exponent.
-/

@[expose] public noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace RapidSequence

/-- The weighted supremum seminorms increase with their exponent. -/
theorem seminorm_monotone : Monotone (seminorm (𝕜 := 𝕜) (E := E)) := by
  intro j k hjk f
  apply seminorm_le_of_forall_le j f (apply_nonneg (seminorm k) f)
  intro n
  have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn'
  calc
    ((n + 1 : ℕ) : ℝ) ^ j * ‖f n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ k * ‖f n‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn hjk) (norm_nonneg _)
    _ ≤ seminorm k f := weight_mul_norm_le_seminorm k n f

end RapidSequence
