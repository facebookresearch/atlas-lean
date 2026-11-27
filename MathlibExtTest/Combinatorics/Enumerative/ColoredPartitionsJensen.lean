/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Polynomial MetaMathlibExt MetaMathlibExt.ColoredPartitionsJensen

-- Ordinary partitions (`r = 1`), degree two: the quadratic Jensen polynomials of `p(n)` are
-- eventually real-rooted.
example : ∀ᶠ n in atTop,
    (∑ j ∈ Finset.range 3, C (((2 : ℕ).choose j : ℝ) *
        ((∑ x ∈ Finset.Nat.antidiagonalTuple 1 (n + j),
          ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).roots.card =
      (∑ j ∈ Finset.range 3, C (((2 : ℕ).choose j : ℝ) *
        ((∑ x ∈ Finset.Nat.antidiagonalTuple 1 (n + j),
          ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).natDegree :=
  eventually_jensen_hyperbolic_coloredPartitions (r := 1) le_rfl (d := 2) (by norm_num)

-- The bridge accepts a sequence whose log-ratio is bounded below but whose expansion has no
-- positive `A`: in degree one every sequence has the expansion, here `α n = 2⁻ⁿ`.
example : ∀ᶠ n in atTop,
    (∑ j ∈ Finset.range 2, C (((1 : ℕ).choose j : ℝ) * (2 : ℝ)⁻¹ ^ (n + j)) * X ^ j).roots.card =
      (∑ j ∈ Finset.range 2, C (((1 : ℕ).choose j : ℝ) * (2 : ℝ)⁻¹ ^ (n + j)) *
        X ^ j).natDegree :=
  (hasLogRatioExpansion_of_le_one _ le_rfl).eventually_card_roots le_rfl
    (Eventually.of_forall fun _ => by positivity)
    ⟨1, Eventually.of_forall fun n => by
      rw [pow_succ, mul_div_cancel_left₀ _ (by positivity)]
      have := Real.log_two_lt_d9
      rw [Real.log_inv]
      linarith⟩
