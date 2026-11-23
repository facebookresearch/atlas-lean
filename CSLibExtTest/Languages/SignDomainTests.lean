/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SignDomain

/-! # Sign domain regression probes -/

open Cslib.AbstractInterpretation

-- Classification of negative, zero, and positive integers.
example : SignType.sign (-3 : ℤ) = -1 := by decide
example : SignType.sign (0 : ℤ) = 0 := by decide
example : SignType.sign (5 : ℤ) = 1 := by decide

-- Every row of the abstract addition table.
example : addSigns (-1) (-1) = {-1} := by decide
example : addSigns (-1) 0 = {-1} := by decide
example : addSigns (-1) 1 = {-1, 0, 1} := by decide
example : addSigns 0 (-1) = {-1} := by decide
example : addSigns 0 0 = {0} := by decide
example : addSigns 0 1 = {1} := by decide
example : addSigns 1 (-1) = {-1, 0, 1} := by decide
example : addSigns 1 0 = {1} := by decide
example : addSigns 1 1 = {1} := by decide

-- Mixed-sign sums reach each sign of the mixed row.
example : SignType.sign ((-5 : ℤ) + 3) = -1 := by decide
example : SignType.sign ((-3 : ℤ) + 3) = 0 := by decide
example : SignType.sign ((-3 : ℤ) + 5) = 1 := by decide
example : SignType.sign ((5 : ℤ) + -3) = 1 := by decide

-- The soundness theorem places each of those sums in the mixed row.
example : SignType.sign ((-5 : ℤ) + 3) ∈ addSigns (SignType.sign (-5)) (SignType.sign 3) :=
  sign_add_mem_addSigns (-5) 3

example : SignType.sign ((-3 : ℤ) + 3) ∈ addSigns (SignType.sign (-3)) (SignType.sign 3) :=
  sign_add_mem_addSigns (-3) 3

-- Rows of the abstract multiplication table, including zero factors.
example : mulSigns 0 (-1) = {0} := by decide
example : mulSigns 1 0 = {0} := by decide
example : mulSigns 0 0 = {0} := by decide
example : mulSigns (-1) (-1) = {1} := by decide
example : mulSigns (-1) 1 = {-1} := by decide
example : mulSigns 1 (-1) = {-1} := by decide
example : mulSigns 1 1 = {1} := by decide

-- Products with a zero factor and with factors of opposite signs.
example : SignType.sign ((0 : ℤ) * -7) = 0 := by decide
example : SignType.sign ((-2 : ℤ) * 5) = -1 := by decide
example : SignType.sign ((-2 : ℤ) * -5) = 1 := by decide

example : SignType.sign ((0 : ℤ) * -7) ∈ mulSigns (SignType.sign 0) (SignType.sign (-7)) :=
  sign_mul_mem_mulSigns 0 (-7)
