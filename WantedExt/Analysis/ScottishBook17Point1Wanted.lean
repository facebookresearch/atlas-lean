/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.ScottishBook17Point1
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook17Point1Wanted

/-- The claim of Problem 17.1 for `C ^ ∞` functions on `ℝ`, the case refuted by
Zahorski's construction. The smoothness order is `(⊤ : ℕ∞)`; a bare `⊤` would
mean analytic. -/
def ScottishBookProblem17Point1SmoothClaim : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
    ∃ (C : Set ℝ) (φ : ℝ → ℝ), IsPerfectSet C ∧ C ⊆ Set.Icc (0 : ℝ) 1 ∧
      AnalyticOn ℝ φ (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ C, f x = φ x

/-- Zahorski's stronger answer: the claim fails already for `C ^ ∞` functions.
Source: Z. Zahorski, Fund. Math. 34 (1947), 183-245, as above. -/
theorem_wanted smoothFunctionPerfectAnalytic_refuted : ¬ ScottishBookProblem17Point1SmoothClaim

end MathlibExt.Analysis.ScottishBook17Point1Wanted
