/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ExtendedTrinomialAlternating
import Mathlib.Tactic.NormNum

/-! # Tests for the alternating extended trinomial convolution -/

open PowerSeries MetaMathlibExt

private noncomputable def E (u : ℂ) (j : ℕ) : ℂ :=
  coeff j ((binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))

example (x : ℂ) : E (-x) 0 * E x 0 = E (-(2 * x)) 0 * E x 0 := by
  simpa [E, Finset.sum_range_succ] using
    (sum_extended_trinomial_alternating_eq (x := x) (n := 0))

example (x : ℂ) :
    E (2 - x) 1 * E x 0 - E (2 - x) 0 * E x 1 = E (2 - 2 * x) 1 * E x 0 := by
  have h := sum_extended_trinomial_alternating_eq (x := x) (n := 1)
  norm_num [E, Finset.sum_range_succ, sub_eq_add_neg] at h ⊢
  exact h

example :
    E (4 - Complex.I) 2 * E Complex.I 0 - E (4 - Complex.I) 1 * E Complex.I 1 +
        E (4 - Complex.I) 0 * E Complex.I 2 =
      E (4 - 2 * Complex.I) 2 * E Complex.I 0 + E (4 - 2 * Complex.I) 0 * E Complex.I 1 := by
  have h := sum_extended_trinomial_alternating_eq (x := Complex.I) (n := 2)
  norm_num [E, Finset.sum_range_succ, sub_eq_add_neg] at h ⊢
  exact h
