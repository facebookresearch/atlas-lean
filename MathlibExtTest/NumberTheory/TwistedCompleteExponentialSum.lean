/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwistedCompleteExponentialSum

/-! # Tests for the lower bound on twisted complete exponential sums -/

open Complex Finset MetaMathlibExt

-- The bound supplies a twist with a natural representative below the modulus.
example (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) :
    ∃ y < p, Real.sqrt p ≤ ‖∑ x ∈ Icc 1 p,
      exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖ := by
  let S (y : ℕ) := ∑ x ∈ Icc 1 p,
    exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)
  obtain ⟨y, hy, hmax⟩ := exists_mem_eq_sup (range p) (nonempty_range_iff.mpr hp.ne_zero)
    (fun y => ‖S y‖₊)
  have h : Real.sqrt p ≤ (((range p).sup fun y => ‖S y‖₊ : NNReal) : ℝ) :=
    sqrt_le_sup_norm_completeSum p hp f
  rw [hmax] at h
  exact ⟨y, mem_range.mp hy, h⟩

-- At the smallest prime, the untwisted linear phase cancels and the other twist adds to two.
example :
    let f : Polynomial ℤ := -Polynomial.X
    let S (y : ℕ) := ∑ x ∈ Icc 1 (2 : ℕ),
      exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / 2)
    S 0 = 0 ∧ S 1 = 2 := by
  have hIcc : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  dsimp only
  simp only [hIcc, sum_pair (by decide : (1 : ℕ) ≠ 2), Polynomial.eval_neg, Polynomial.eval_X]
  norm_num
  rw [show -(2 * (Real.pi : ℂ) * I) / 2 = -(Real.pi * I) by ring, exp_neg_pi_mul_I,
    show -(2 * (Real.pi : ℂ) * I * 2) / 2 = -(2 * Real.pi * I) by ring, exp_neg,
    exp_two_pi_mul_I]
  norm_num
