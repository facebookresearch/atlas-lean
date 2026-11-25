/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open ArithmeticFunction MetaMathlibExt

-- The hypotheses characterize the identity as an arithmetic function, including its value at zero.
example (f : ArithmeticFunction ℂ) :
    (f.IsMultiplicative ∧
      (∀ x y : Fin 4 → ℕ, (∀ i, 0 < x i) → (∀ i, 0 < y i) →
        f (∑ i, (x i ^ 2 + y i ^ 2)) = ∑ i, f (x i ^ 2 + y i ^ 2)) ∧ f 2 ≠ 0) ↔
      f = (ArithmeticFunction.id : ArithmeticFunction ℂ) := by
  constructor
  · rintro ⟨hf, hadd, h2⟩
    ext n
    cases n with
    | zero => simp
    | succ n =>
      simpa using multiplicative_additive_eight_squares_eq_id f hf hadd h2 _ (Nat.succ_pos n)
  · rintro rfl
    refine ⟨isMultiplicative_id.natCast, ?_, by norm_num⟩
    intro x y _ _
    simp
