/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GouldTrinomialIdentities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the Gould-type binomial and trinomial identities -/

open PowerSeries MetaMathlibExt

private noncomputable def E (u : ℂ) (j : ℕ) : ℂ :=
  coeff j ((binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))

-- At degree zero both convolution ranges are singletons.
example (x y : ℂ) :
    Ring.choose x 0 * Ring.choose (y - 3 * x) 0 = Ring.choose x 0 * Ring.choose y 0 ∧
      E (-x) 0 * Ring.choose x 0 = Ring.choose x 0 := by
  simpa [E, Finset.sum_range_succ] using
    (sum_choose_gould_and_extended_trinomial (x := x) (y := y) (n := 0))

-- Degree three is the first degree at which the cubic substitution contributes a k = 1 term.
example (x y : ℂ) :
    Ring.choose x 0 * Ring.choose (y - 3 * x) 3 + Ring.choose x 1 * Ring.choose (y - 3 * x) 0 =
      Ring.choose x 0 * Ring.choose y 3 - 3 * Ring.choose x 1 * Ring.choose (y - 2) 2 +
        9 * Ring.choose x 2 * Ring.choose (y - 4) 1 - 27 * Ring.choose x 3 * Ring.choose (y - 6) 0 := by
  have h := (sum_choose_gould_and_extended_trinomial x y 3).1
  norm_num [Finset.sum_range_succ] at h ⊢
  convert h using 1
  ring

-- A non-real exponent, with a negative sign on both the cubic term and the odd-degree RHS.
example :
    E (-Complex.I) 3 * Ring.choose Complex.I 0 - E (-Complex.I) 0 * Ring.choose Complex.I 1 =
      -Ring.choose Complex.I 3 := by
  have h := (sum_choose_gould_and_extended_trinomial Complex.I 0 3).2
  norm_num [E, Finset.sum_range_succ, sub_eq_add_neg] at h ⊢
  exact h
