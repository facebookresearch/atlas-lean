/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSmallCases
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- The intersection of order zero and degree zero keeps the constant term, even at `y = 0`.
example (x : ℂ) : alternatingBinomialPowerSum 0 0 x 0 = 1 := by
  simpa using (alternatingBinomialPowerSum_small_cases x 0 0 0).1

example (x y : ℂ) : alternatingBinomialPowerSum 0 3 x y = 0 := by
  norm_num [(alternatingBinomialPowerSum_small_cases x y 0 3).2.2.2.2.2.1]

-- The subdiagonal starts at degree one, with order zero.
example (x y : ℂ) : alternatingBinomialPowerSum 1 0 x y = y := by
  simpa using (alternatingBinomialPowerSum_small_cases x y 1 0).2.2.2.1 (by decide)

example (x y : ℂ) : alternatingBinomialPowerSum 3 3 x y = -6 * x ^ 3 := by
  norm_num [Nat.factorial, (alternatingBinomialPowerSum_small_cases x y 3 3).2.2.2.2.1]

example : ∑ m ∈ range 4, alternatingBinomialPowerSum 3 m 2 5 = 27 := by
  norm_num [(alternatingBinomialPowerSum_small_cases 2 5 3 0).2.2.2.2.2.2]
