/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SchutzKellyBinomialSum

open MetaMathlibExt
open scoped BigOperators

-- Empty shifted sum and the zero upper index.
example : 1 + (∑ i ∈ Finset.range (0 + 1), (0 - 0 * i).choose (i + 1)) +
    (∑ i ∈ Finset.range 0, (0 - 0 * i - 0).choose (i + 1)) = 1 := by
  rw [one_add_sum_choose_add_sum_choose 0 0 0]
  decide

-- The natural upper index truncates at zero in the term at i = 2.
example : 1 + (∑ i ∈ Finset.range (2 + 1), (3 - 2 * i).choose (i + 1)) +
    (∑ i ∈ Finset.range 2, (3 - 2 * i - 2).choose (i + 1)) = 5 := by
  rw [one_add_sum_choose_add_sum_choose 2 3 2]
  decide
