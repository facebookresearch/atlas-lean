/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MinusculePolynomialLogConcavity
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

-- The all-indices API covers an empty row, the truncated predecessor, and the upper boundary.
example : (minusculePolynomialA 0).coeff 1 * (minusculePolynomialA 0).coeff 3 ≤
    (minusculePolynomialA 0).coeff 2 ^ 2 :=
  minusculePolynomialA_coeff_logConcave 0 2

example : (minusculePolynomialA 2).coeff 0 * (minusculePolynomialA 2).coeff 1 ≤
    (minusculePolynomialA 2).coeff 0 ^ 2 :=
  minusculePolynomialA_coeff_logConcave 2 0

example : (minusculePolynomialA 4).coeff 3 * (minusculePolynomialA 4).coeff 5 ≤
    (minusculePolynomialA 4).coeff 4 ^ 2 :=
  minusculePolynomialA_coeff_logConcave 4 4

-- The first row with three nonzero coefficients has a strict interior inequality.
example : (minusculePolynomialA 4).coeff 1 * (minusculePolynomialA 4).coeff 3 <
    (minusculePolynomialA 4).coeff 2 ^ 2 := by
  norm_num [minusculePolynomialA, show Finset.Icc 1 (4 - 1) = {1, 2, 3} by decide,
    finsetSum_coeff, coeff_C_mul_X_pow, Nat.choose]
