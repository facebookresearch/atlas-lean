/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.AevalLimitAtZero

@[expose] public section

-- Consumer with the original binders.
example (R D : ℕ) (N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y →
      Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
    Polynomial.aeval (N 0) q = 0 :=
  Polynomial.aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero R D N q h

-- The positivity hypothesis matters: with `q = X` and the constant family
-- `N 0 = 1`, the conclusion `aeval 1 X = 0` is false.
example : ¬ Polynomial.aeval (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (Polynomial.X : Polynomial ℂ) = 0 := by
  rw [Polynomial.aeval_X]
  exact one_ne_zero
