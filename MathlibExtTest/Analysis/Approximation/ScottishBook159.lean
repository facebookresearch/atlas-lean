/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Approximation.ScottishBook159
import Mathlib.Tactic.ByContra

open Set
open MathlibExt.Analysis.ScottishBook159Wanted

-- The counterexample is chosen after the budget N, but before the approximant n.
example (a : ℕ → ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ f : ℝ → ℝ,
    ContinuousOn f (Icc 0 1) ∧ f 0 = 0 ∧
    (∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc 0 1) ∧
    ∀ n ≤ N, ∃ x ∈ Icc (0 : ℝ) 1,
      ε ≤ dist (f x) (∑ k ∈ Finset.range (n + 1), a k * x ^ k) := by
  by_contra! h
  exact problem159Refuted ⟨a, h⟩
