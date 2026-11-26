/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.RestrictedCombinations

open MetaMathlibExt PowerSeries

-- The constant term counts the empty subset of the empty interval.
example : restrictedCombinationTotal {1, 4} 0 = 1 := by
  simpa using congrArg (constantCoeff (R := ℤ)) restrictedCombinationTotal_one_four_genFun

-- At length four the gap four cannot occur; at length five it excludes {1, 5}.
example : restrictedCombinationTotal {1, 4} 4 = 8 := by decide
example : ({1, 5} : Finset ℕ) ∉ restrictedCombinations {1, 4} 5 2 := by decide
example : restrictedCombinationTotal {1, 4} 5 = 11 := by decide

-- The degree-seven coefficient is the first beyond the numerator and uses the constant count.
example : restrictedCombinationTotal {1, 4} 7 = 25 := by
  let a := restrictedCombinationTotal {1, 4}
  let f : PowerSeries ℤ := mk fun n => (a n : ℤ)
  have h := congrArg (coeff (R := ℤ) 7) restrictedCombinationTotal_one_four_genFun
  change coeff 7 (f * _) = _ at h
  have h₅ : f * (2 * X ^ 5) = 2 * (f * X ^ 5) := mul_left_comm _ _ _
  norm_num [mul_add, mul_sub, h₅, coeff_succ_mul_X 6, coeff_mul_X_pow', coeff_one, coeff_X,
    coeff_X_pow, f] at h
  have hinit : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 5 ∧ a 4 = 8 ∧ a 6 = 17 := by
    decide
  obtain ⟨h0, h1, h2, h3, h4, h6⟩ := hinit
  rw [h0, h1, h2, h3, h4, h6] at h
  change a 7 = 25
  omega
