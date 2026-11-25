/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingCentralBinomialConvolution

open Finset MetaMathlibExt

example :
    ∑ k ∈ range (0 + 1), (-1 : ℤ) ^ k * ((2 * k).choose k : ℤ) *
        ((2 * (0 - k)).choose (0 - k)) = 1 := by
  rw [sum_neg_one_pow_centralBinom_mul_centralBinom]
  decide

example :
    ∑ k ∈ range (4 + 1), (-1 : ℤ) ^ k * ((2 * k).choose k : ℤ) *
        ((2 * (4 - k)).choose (4 - k)) = 96 := by
  rw [sum_neg_one_pow_centralBinom_mul_centralBinom]
  decide

example :
    ∑ k ∈ range (3 + 1), (-1 : ℤ) ^ k * ((2 * k).choose k : ℤ) *
        ((2 * (3 - k)).choose (3 - k)) = 0 := by
  rw [sum_neg_one_pow_centralBinom_mul_centralBinom]
  decide
