/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook17Point1Wanted

/-- A perfect set: closed, nonempty, with no isolated points. -/
def IsPerfectSet (s : Set ℝ) : Prop :=
  IsClosed s ∧ s.Nonempty ∧ ∀ x ∈ s, x ∈ closure (s \ {x})

/-- Ulam's Problem 17.1 from the Scottish Book: for every continuous `f` on
`[0, 1]`, do there exist a perfect set `C` in `[0, 1]` and an analytic
function `φ` with `f x = φ x` for every `x ∈ C`? The claim is stated for
`C ^ ∞` functions, which is the case refuted by Zahorski's construction. -/
def ScottishBookProblem17Point1Claim : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ ⊤ f →
    ∃ (C : Set ℝ) (φ : ℝ → ℝ), IsPerfectSet C ∧ C ⊆ Set.Icc (0 : ℝ) 1 ∧
      AnalyticOn ℝ φ (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ C, f x = φ x

/--
Problem 17.1 is false: the answer is negative. Source: S. Ulam, Problem 17.1
of the Scottish Book; Z. Zahorski gave a negative answer by constructing a
`C ^ ∞` function that agrees with every real-analytic function on at most
finitely many points, so no nonempty perfect set `C` can work for it: Z.
Zahorski, "Sur l'ensemble des points singuliers d'une fonction d'une
variable reelle admettant les derivees de tous les ordres", Fund. Math. 34
(1947), 183-245. The 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867) confirms the negative solution.
-/
theorem_wanted continuousFunctionPerfectAnalytic_refuted : ¬ ScottishBookProblem17Point1Claim

end MathlibExt.Analysis.ScottishBook17Point1Wanted
