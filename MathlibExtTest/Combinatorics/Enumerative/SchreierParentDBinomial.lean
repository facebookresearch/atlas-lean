/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SchreierParentDBinomial

open MetaMathlibExt

-- At n = 1 the numerator truncates to zero, but the constant term is one.
example : schreierParentD 2 1 = 1 := by
  rw [schreierParentD_eq_sum_choose (u := 2) (n := 1) (by decide) (by decide)]
  decide

-- At u = 3 the first positive-index term appears precisely at n = 6.
example : schreierParentD 3 5 = 1 ∧ schreierParentD 3 6 = 2 := by
  rw [schreierParentD_eq_sum_choose (u := 3) (n := 5) (by decide) (by decide),
    schreierParentD_eq_sum_choose (u := 3) (n := 6) (by decide) (by decide)]
  decide

-- Several binomial terms contribute; the last term in the stated range vanishes.
example : schreierParentD 3 13 = 5 := by
  rw [schreierParentD_eq_sum_choose (u := 3) (n := 13) (by decide) (by decide)]
  decide

-- The exposed recursive definition gives the same value independently of the sum.
example : schreierParentD 3 13 = 5 := by decide +kernel
