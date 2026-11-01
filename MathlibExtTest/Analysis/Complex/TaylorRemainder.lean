/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.TaylorRemainder

/-!
# Tests for Taylor expansion with a holomorphic remainder
-/

@[expose] public section

open Complex

/-- The expansion exists for `exp` at `0` on all of `ℂ`. -/
example : ∃ b : ℕ → ℂ, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Set.univ ∧
    ∀ s ∈ Set.univ, Complex.exp s =
      (∑ j ∈ Finset.range 3, b j * (s - 0) ^ j) + (s - 0) ^ 3 * g s :=
  Complex.differentiable_exp.differentiableOn.exists_eq_sum_add_pow_mul Filter.univ_mem 3

/-- On a non-open neighbourhood (a closed ball). -/
example : ∃ b : ℕ → ℂ, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.closedBall 1 (1 / 2)) ∧
    ∀ s ∈ Metric.closedBall (1 : ℂ) (1 / 2), 1 / s =
      (∑ j ∈ Finset.range 2, b j * (s - 1) ^ j) + (s - 1) ^ 2 * g s := by
  refine DifferentiableOn.exists_eq_sum_add_pow_mul ?_
    (Metric.closedBall_mem_nhds 1 (by norm_num)) 2
  intro s hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [Metric.mem_closedBall] at hs
    norm_num at hs
  exact (differentiableAt_const _ |>.div differentiableAt_id hs0).differentiableWithinAt

/-- `n = 0` is the trivial expansion `f = 1 · f`. -/
example (f : ℂ → ℂ) (hf : Differentiable ℂ f) : ∃ b : ℕ → ℂ, ∃ g : ℂ → ℂ,
    DifferentiableOn ℂ g Set.univ ∧ ∀ s ∈ Set.univ, f s =
      (∑ j ∈ Finset.range 0, b j * (s - 0) ^ j) + (s - 0) ^ 0 * g s :=
  hf.differentiableOn.exists_eq_sum_add_pow_mul Filter.univ_mem 0

/-- With explicit coefficients: `exp s = 1 + s + s ^ 2 / 2 + s ^ 3 g(s)`. -/
example : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Set.univ ∧
    ∀ s : ℂ, Complex.exp s = 1 + s + s ^ 2 / 2 + s ^ 3 * g s := by
  obtain ⟨g, hg, h⟩ :=
    Complex.differentiable_exp.differentiableOn.eq_sum_iteratedDeriv_add_pow_mul
      (a := 0) Filter.univ_mem 3
  refine ⟨g, hg, fun s => ?_⟩
  rw [h s]
  simp [Finset.sum_range_succ, iteratedDeriv_eq_iterate, Nat.factorial]
  ring
