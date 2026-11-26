/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetFussCatalan

open MetaMathlibExt

-- In size one the determinant is the first generalized Fuss–Catalan number, `r`.
example (p r : ℕ) : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) 1 = r := by
  simpa using toeplitzHessenbergDet_fussCatalan p r 1 le_rfl

-- The Catalan case gives the negative determinant `1² - 2` in size two.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 1 : ℚ)) 2 = -1 := by
  rw [toeplitzHessenbergDet_fussCatalan 2 1 2 (by decide)]
  norm_num [Ring.choose_one_right]

-- The upper index is `-2`. The generalized binomial gives `3`, not zero.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 1 i 3 : ℚ)) 2 = 3 := by
  rw [toeplitzHessenbergDet_fussCatalan 1 3 2 (by decide)]
  norm_num [Ring.choose_one_right]

-- Check the same value directly from the `2 × 2` determinant, without the general formula.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 1 i 3 : ℚ)) 2 = 3 := by
  rw [toeplitzHessenbergDet_two, show generalizedFussCatalanNumber 1 2 3 = 6 by decide]
  norm_num [generalizedFussCatalanNumber_one]

-- Both parameters may be zero, even though the source excludes that case.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 0 i 0 : ℚ)) 2 = 0 := by
  rw [toeplitzHessenbergDet_fussCatalan 0 0 2 (by decide)]
  norm_num
