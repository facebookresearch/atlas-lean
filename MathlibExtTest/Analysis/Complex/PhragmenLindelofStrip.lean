/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.PhragmenLindelofStrip

/-!
# Tests for Phragmén–Lindelöf on vertical strips with pointwise bounds
-/

open Complex Set

@[expose] public section

/-- `exp s`, bounded by `e` on the edges of `0 ≤ Re s ≤ 1`, is bounded on the strip. -/
example : ∃ B' : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖Complex.exp s‖ ≤ B' :=
  PhragmenLindelof.vertical_strip_of_le_exp_rpow (α := 0)
    (Differentiable.diffContOnCl differentiable_exp)
    ⟨Real.exp 1, 0, fun s _ h2 _ => by
      rw [norm_exp, Real.rpow_zero, mul_comm, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)⟩
    ⟨Real.exp 1, fun s hs => by
      rw [norm_exp]
      exact Real.exp_le_exp.2 (by rcases hs with h | h <;> simp [h])⟩

/-- Polynomial growth: `‖s‖ ≤ C |Im s|` on the edges of `0 ≤ Re s ≤ 1` propagates inside. -/
example : ∃ C, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1 ≤ |s.im| → ‖s‖ ≤ C * |s.im| ^ (1 : ℝ) :=
  PhragmenLindelof.vertical_strip_le_mul_rpow (f := id) (α := 1)
    (Differentiable.diffContOnCl differentiable_id)
    ⟨1, 0, fun s h1 h2 _ => by
      have := norm_le_abs_re_add_abs_im s
      have h3 : |s.re| ≤ 1 := abs_le.2 ⟨by linarith, h2⟩
      have h4 := Real.add_one_le_exp (|s.im| ^ (1 : ℝ))
      simp only [Real.rpow_one] at h4 ⊢
      simp only [id, one_mul]
      linarith⟩
    ⟨2, fun s hs ht => by
      have := norm_le_abs_re_add_abs_im s
      have h3 : |s.re| ≤ 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
      simp only [Real.rpow_one, id]
      linarith⟩
