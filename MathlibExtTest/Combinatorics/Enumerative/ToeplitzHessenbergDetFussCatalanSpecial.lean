/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetFussCatalanSpecial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The first family vanishes at its lowest degree, as the `2 × 2` expansion `3² - 9` confirms.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) 2 = 0 := by
  simpa using toeplitzHessenbergDet_fussCatalan_special.1 2 le_rfl

example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) 2 = 0 := by
  rw [toeplitzHessenbergDet_two, show generalizedFussCatalanNumber 2 2 3 = 9 by decide]
  norm_num [generalizedFussCatalanNumber_one]

-- The second family also starts at zero, `C₂ - 2 C₁ = 0`; one degree lower the formula would fail.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) 3 = 0 := by
  simpa [catalan_two] using toeplitzHessenbergDet_fussCatalan_special.2.1 3 le_rfl

example : (-1) ^ (2 - 1) * toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) 2 ≠
      (catalan (2 - 1) : ℚ) - 2 * catalan (2 - 2) := by
  rw [toeplitzHessenbergDet_two, show generalizedFussCatalanNumber 2 2 4 = 14 by decide]
  norm_num [generalizedFussCatalanNumber_one]

-- In degree one the determinant is the entry `A₁(3, r) = r`.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 2 : ℚ)) 1 = 2 := by
  simpa using toeplitzHessenbergDet_fussCatalan_special.2.2.2 1 le_rfl

-- `D₄(3, 1) = binom(10, 3)/4 = 30`, so the determinant of size four is `-30`.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 1 : ℚ)) 4 = -30 := by
  have h := toeplitzHessenbergDet_fussCatalan_special.2.2.1 4 (by decide)
  norm_num [Nat.choose] at h
  linarith

-- At the lower endpoint for the H-shift, the sign is negative.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) 2 = -3 := by
  have h := toeplitzHessenbergDet_ternary.1 2 le_rfl
  norm_num [Nat.choose] at h
  exact h

-- Independently, the size-two determinant is H₂² - H₃ = 3² - 12.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) 2 = -3 := by
  rw [toeplitzHessenbergDet_two]
  norm_num [show generalizedFussCatalanNumber 3 2 1 = 3 by decide,
    show generalizedFussCatalanNumber 3 3 1 = 12 by decide]

-- The J-shift starts at J₀, and at size one the determinant equals H₁.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then -1 else (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) 1 = 1 := by
  simpa [generalizedFussCatalanNumber_one] using toeplitzHessenbergDet_ternary.2 1 le_rfl

-- At size two the superdiagonal contributes with the opposite sign: J₀² + J₁ = H₂.
example : toeplitzHessenbergDet
    (fun i => if i = 0 then -1 else (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) 2 =
      (generalizedFussCatalanNumber 3 2 1 : ℚ) := by
  rw [toeplitzHessenbergDet_two]
  norm_num [show generalizedFussCatalanNumber 3 0 2 = 1 by decide,
    generalizedFussCatalanNumber_one, show generalizedFussCatalanNumber 3 2 1 = 3 by decide]
