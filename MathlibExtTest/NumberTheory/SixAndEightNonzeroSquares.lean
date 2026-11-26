/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SixAndEightNonzeroSquares

open MetaMathlibExt

example : ∃ a : Fin 6 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 20 :=
  sum_six_and_eight_nonzero_squares.1 20 (by decide)

example : ∃ a : Fin 8 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 22 :=
  sum_six_and_eight_nonzero_squares.2 22 (by decide)

example : ∃ a : Fin 8 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 1000 :=
  sum_six_and_eight_nonzero_squares.2 1000 (by decide)
