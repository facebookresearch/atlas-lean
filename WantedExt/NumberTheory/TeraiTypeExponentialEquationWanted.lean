/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WantedExt.NumberTheory.QuadraticForms.KroneckerFormSumsWanted

/-!
# The exponential equation `(10m² + 1)^x + (15m² - 1)^y = (5m)^z`

Statement-only target from Kalyan Chakraborty and Meenu Sharma, *A Note on Terai's Conjecture
Related to Exponential Diophantine Equations*, INTEGERS 26 (2026), Article A67.
-/

namespace MetaMathlibExt

@[expose] public section

/-- For every integer `m > 1`, the only solution of
`(10m² + 1)^x + (15m² - 1)^y = (5m)^z` in positive integers is `(x, y, z) = (1, 1, 2)`.
Natural-number subtraction in `15 m² - 1` is exact since `m > 1`.

Source: Kalyan Chakraborty and Meenu Sharma, *A Note on Terai's Conjecture Related to Exponential
Diophantine Equations*, INTEGERS 26 (2026), Article A67, Theorem 2 (`integers-2026-A67-thm-2`). -/
public theorem_wanted terai_ten_fifteen_five_eq_one_one_two {m x y z : ℕ} (hm : 1 < m)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (10 * m ^ 2 + 1) ^ x + (15 * m ^ 2 - 1) ^ y = (5 * m) ^ z) :
    x = 1 ∧ y = 1 ∧ z = 2

/-- **Theorem 3** (quoted from Hua's textbook). For every positive integer `D`, the class number
of primitive positive definite binary quadratic forms of discriminant `-4D` satisfies
`h(-4D) < (4/π) √D log(2e√D)`. "Class number of positive binary quadratic forms" is read as the
standard primitive (Gauss) class number `gaussClassNumber`: the number of primitive
Gauss-reduced forms of discriminant `-4D`.

Source: Kalyan Chakraborty and Meenu Sharma, *A Note on Terai's Conjecture Related to Exponential
Diophantine Equations*, INTEGERS 26 (2026), Article A67, Theorem 3 (`integers-2026-A67-thm-3`). -/
public theorem_wanted gaussClassNumber_neg_four_mul_lt (D : ℕ) (hD : 0 < D) :
    (gaussClassNumber (-4 * D) : ℝ) <
      4 / Real.pi * Real.sqrt D * Real.log (2 * Real.exp 1 * Real.sqrt D)

end

end MetaMathlibExt
