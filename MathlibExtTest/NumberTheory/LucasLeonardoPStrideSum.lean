/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasLeonardoPStrideSum
import Mathlib.Tactic.Ring

/-!
# Tests for the stride sum of Lucas–Leonardo `p`-numbers
-/

open MetaMathlibExt

-- With no stride terms beyond the first, the identity reads `R_{p,0} = R_{p,1} + p(p + 1)`.
example (p : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p 0 = lucasLeonardoP p 1 + p * ((p : ℤ) + 1) := by
  have h := sum_lucasLeonardoP_stride p 0 hp
  simp only [Finset.sum_range_one, Nat.mul_zero, Nat.zero_add] at h
  rw [h]
  push_cast
  ring

-- For p = 2 and n = 2: `R_0 + R_3 + R_6 = 7 + 10 + 28 = 45 = R_7 - 2 * (2 - 2 - 1) = 43 + 2`.
example : ∑ i ∈ Finset.range 3, lucasLeonardoP 2 (3 * i) = 45 := by
  rw [sum_lucasLeonardoP_stride 2 2 (by decide)]
  decide
