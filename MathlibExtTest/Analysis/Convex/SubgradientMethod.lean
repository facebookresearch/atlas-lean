/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.SubgradientMethod
import Mathlib.Basic.Real.Sign

open Real

namespace MetaMathlibExt

-- The subgradient method on `f x = |x|` with subgradients `sign x`, `B = 1` and `D = |x₀|`:
-- after `t ≥ 1` steps some iterate has `|X k| ≤ |x₀| (2 + log t) / (2 √t)`.
example (x₀ : ℝ) (hx₀ : x₀ ≠ 0) (t : ℕ) (ht : 0 < t) :
    let X : ℕ → ℝ := fun k => Nat.rec x₀
      (fun j xj => xj - (|x₀| / (1 * √((j : ℝ) + 1))) * Real.sign xj) k
    ∃ k < t, |X k| ≤ |x₀| * 1 * (2 + log t) / (2 * √t) := by
  intro X
  have hsub : ∀ k y, |X k| + inner ℝ (Real.sign (X k)) (y - X k) ≤ |y| := by
    intro k y
    simp only [RCLike.inner_apply, conj_trivial]
    rcases lt_trichotomy (X k) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]
      have := neg_abs_le y
      nlinarith
    · rw [h, Real.sign_zero]; simp
    · rw [Real.sign_of_pos h, abs_of_pos h]
      have := le_abs_self y
      nlinarith
  have hg : ∀ k, ‖Real.sign (X k)‖ ≤ 1 := by
    intro k
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy (X k) 0 with h | h | h
    · simp [Real.sign_of_neg h]
    · simp [h]
    · simp [Real.sign_of_pos h]
  have h := subgradient_method_rate (E := ℝ) (f := fun x => |x|) (B := 1) (D := |x₀|)
    one_pos (abs_pos.mpr hx₀) hsub hg (xstar := 0) (by simp [X])
    (fun k => by simp only [X, smul_eq_mul]) ht
  simpa using h

end MetaMathlibExt
