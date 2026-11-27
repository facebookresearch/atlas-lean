/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasLeonardoPPrefixSum

/-! # Tests for prefix sums of Lucas-Leonardo `p`-numbers -/

open MetaMathlibExt

-- For p = 2 the first term is 7; the shifted term is 10.
example : ∑ i ∈ Finset.range 1, lucasLeonardoP 2 i = 7 := by
  rw [sum_lucasLeonardoP 2 0 (by decide)]
  decide

-- For p = 1 the five terms are 3, 1, 5, 7, and 13.
example : ∑ i ∈ Finset.range 5, lucasLeonardoP 1 i = 29 := by
  rw [sum_lucasLeonardoP 1 4 (by decide)]
  decide
