/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RiordanNumberEvenLogConvex

open MetaMathlibExt

example : riordanNumber 2 ^ 2 ≤ riordanNumber 0 * riordanNumber 4 :=
  riordanNumber_even_logConvex 0

-- The first two comparisons use the even terms 1, 1, 3, 15.
example : riordanNumber 0 = 1 ∧ riordanNumber 2 = 1 ∧
    riordanNumber 4 = 3 ∧ riordanNumber 6 = 15 := by
  simp only [riordanNumber, catalan_eq_centralBinom_div]
  decide
