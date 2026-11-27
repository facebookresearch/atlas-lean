/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarHarmonicReciprocal

/-! # Small cases of the harmonic identity for Sabar's triangle -/

open MetaMathlibExt

private def weightedRow (n : ℕ) : ℚ :=
  (1 / (n : ℚ)) * ∑ i ∈ Finset.range n, 1 / ((n - 1).choose i : ℚ) +
    ∑ i ∈ Finset.range (n - 1), (-1 : ℚ) ^ (n - i) * sabarNumber (n - 1) i / ((n - i : ℕ) : ℚ)

-- At the lower endpoint the Sabar correction has one term.
example : harmonic 2 = weightedRow 2 :=
  harmonic_eq_sum_inv_choose_add_sum_sabarNumber 2 (by decide)

-- Evaluate both parities independently, including the nontrivial interior binomial at `n = 3`.
example : weightedRow 2 = 3 / 2 ∧ weightedRow 3 = 11 / 6 := by decide +kernel
