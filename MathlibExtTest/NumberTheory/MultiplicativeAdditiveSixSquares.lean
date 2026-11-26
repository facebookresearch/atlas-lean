/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditiveSixSquares

namespace MathlibExtTest.NumberTheory.MultiplicativeAdditiveSixSquares

open ArithmeticFunction MetaMathlibExt

-- The theorem applied at a concrete positive integer.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) : f 42 = 42 :=
  multiplicative_additive_six_squares_eq_id f hf hadd h2 42 (by decide)

-- Corollary: such a function is injective on positive integers.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : f m = f n) : m = n := by
  have hm' := multiplicative_additive_six_squares_eq_id f hf hadd h2 m hm
  have hn' := multiplicative_additive_six_squares_eq_id f hf hadd h2 n hn
  exact Nat.cast_injective (hm'.symm.trans (h.trans hn'))

end MathlibExtTest.NumberTheory.MultiplicativeAdditiveSixSquares
