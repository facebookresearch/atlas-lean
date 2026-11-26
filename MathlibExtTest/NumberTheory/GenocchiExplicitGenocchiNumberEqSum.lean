/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenocchiExplicitGenocchiNumberEqSum
import Mathlib.Tactic.NormNum

/-!
# Tests of the explicit Genocchi formula

The Stirling-sum formula gives the second and fourth Genocchi numbers.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli
and Genocchi Numbers", Journal of Integer Sequences 28 (2025), Article 25.6.7, Theorem 1.
-/

namespace MathlibExtTest.NumberTheory.GenocchiExplicitGenocchiNumberEqSum

example : MetaMathlibExt.genocchiNumber 2 = -1 := by
  have h := MathlibExt.NumberTheory.GenocchiExplicitWanted.genocchiNumber_eq_sum
    2 1 (by decide) (by decide) (by decide)
  norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.stirlingSecond_succ_succ, Nat.factorial] at h
  exact h

example : MetaMathlibExt.genocchiNumber 4 = 1 := by
  have h := MathlibExt.NumberTheory.GenocchiExplicitWanted.genocchiNumber_eq_sum
    4 2 (by decide) (by decide) (by decide)
  norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.stirlingSecond_succ_succ, Nat.factorial] at h
  exact h

end MathlibExtTest.NumberTheory.GenocchiExplicitGenocchiNumberEqSum
