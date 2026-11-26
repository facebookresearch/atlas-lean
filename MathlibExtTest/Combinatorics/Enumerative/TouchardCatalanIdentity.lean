/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity

open Finset MetaMathlibExt

example :
    ∑ k ∈ range (3 + 1), ((3 : ℕ).choose k : ℚ) * (2 * k + 1) / (k + 2) *
      2 / 2 ^ k * catalan k = 19 / 2 := by
  rw [sum_choose_two_mul_add_one_div_catalan]
  decide +kernel

example :
    ∑ k ∈ range (4 + 1), ((4 : ℕ).choose k : ℚ) * (2 * k + 1) / (k + 2) *
      2 / 2 ^ k * catalan k = 177 / 8 := by
  rw [sum_choose_two_mul_add_one_div_catalan]
  decide +kernel
