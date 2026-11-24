/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.Gutkovskiy

open MetaMathlibExt

-- The odd term at index 4 is excluded from the prefix at 4 and included at 5.
example : (∑ i ∈ Finset.range 4, gutkovskiy i % 2) = 1 := by
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add 4
  have h₄ : gutkovskiy 4 = 3 := by decide +kernel
  rw [h₄] at h
  omega

example : (∑ i ∈ Finset.range 5, gutkovskiy i % 2) = 2 := by
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add 5
  have h₅ : gutkovskiy 5 = 4 := by decide +kernel
  rw [h₅] at h
  omega
