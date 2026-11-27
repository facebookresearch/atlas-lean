/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialStirling
import Mathlib.Tactic.NormNum

/-! # Small cases of the generalized Stirling polynomials and the coefficients `α_k` -/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- The recurrence `2 α_{k+2} + 2 α_{k+1} + α_k = 0` from `α_0 = 1`, `α_1 = 0`.
example : eulerAlpha 2 = -1 / 2 := by norm_num [eulerAlpha]

example : eulerAlpha 4 = -1 / 4 := by norm_num [eulerAlpha]

-- The zeroth generalized Stirling polynomial is the plain power.
example (n : ℕ) : genStirlingPoly n 0 = X ^ n := by simp [genStirlingPoly]
