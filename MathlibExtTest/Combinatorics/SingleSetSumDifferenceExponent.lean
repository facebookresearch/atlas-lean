/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SingleSetSumDifferenceExponent

/-! # Tests for the single-set sum-difference exponent -/

open MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted
open scoped Pointwise

-- Unfolding the proposition gives the claimed infimum of the admissible exponents.
example : sInf {θ : ℝ | IsAdmissibleExponent θ} = 2 :=
  singleSetSumDifferenceExponent_eq_two_holds

-- A singleton gives equality for every exponent.
example (x : ℤ) (θ : ℝ) : let A : Finset ℤ := {x}
    ((A + A).card : ℝ) / A.card = (((A - A).card : ℝ) / A.card) ^ θ := by
  simp

-- A two-element set already rules out exponent zero.
example : ¬ IsAdmissibleExponent 0 := by
  intro h
  let A : Finset ℤ := {0, 1}
  have hA : A.Nonempty := by decide
  have hs : (A + A).card = 3 := by decide
  have hc : A.card = 2 := by decide
  have hbound := h A hA
  norm_num [hs, hc, Real.rpow_eq_pow] at hbound
