/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FenceTilingSum

namespace MetaMathlibExt

open Finset

-- Direct enumeration with distinct weights, including the empty and one-cell boards.
example : fenceTilingSum (2 : ℕ) 3 0 = 1 := by decide
example : fenceTilingSum (2 : ℕ) 3 1 = 4 := by decide
example : fenceTilingSum (2 : ℕ) 3 2 = 49 := by decide
example : fenceTilingSum (2 : ℕ) 3 4 = 3025 := by decide

-- At n = 2 both intervals are empty; at n = 4 both contribute a term.
example {R : Type*} [CommSemiring R] (a b : R) :
    fenceTilingSum a b 2 = b ^ 2 * fenceTilingSum a b 1 + (2 * a * b + 1) * fenceTilingSum a b 0 := by
  have h₁ : Icc 2 (2 / 2 : ℕ) = ∅ := by decide
  have h₂ : Icc 1 (2 / 2 - 1 : ℕ) = ∅ := by decide
  simpa only [h₁, h₂, sum_empty, mul_zero, add_zero] using
    fenceTilingSum_even a b (n := 2) (by decide) (by decide)

example {R : Type*} [CommSemiring R] (a b : R) :
    fenceTilingSum a b 4 = b ^ 2 * fenceTilingSum a b 3 + (2 * a * b + 1) * fenceTilingSum a b 2 +
      2 * a * b * fenceTilingSum a b 0 + 2 * b ^ 2 * fenceTilingSum a b 1 := by
  have h₁ : Icc 2 (4 / 2 : ℕ) = {2} := by decide
  have h₂ : Icc 1 (4 / 2 - 1 : ℕ) = {1} := by decide
  simpa only [h₁, h₂, sum_singleton] using
    fenceTilingSum_even a b (n := 4) (by decide) (by decide)

end MetaMathlibExt
