/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The first recursive term detects the missing factor in the printed formula.
example : superLeonardoP 1 2 (fun _ => 1) 2 = 4 := by
  rw [superLeonardoP_eq_sum_choose 1 2 (by decide) _ 2 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- All three initial values and the accumulated increment have distinct coefficients.
example (k : ℕ) (x : ℕ → ℝ) :
    superLeonardoP 2 k x 6 = 3 * x 2 + (2 * x 0 + x 1) + 5 * k := by
  rw [superLeonardoP_eq_sum_choose 2 k (by decide) x 6 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]
