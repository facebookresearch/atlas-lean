/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook159Wanted

/-- The claim of Problem 159: there is a power series `P(x) = ∑ aₙ xⁿ` such
that for every `ε > 0` there is `N(ε)` with the property that for every
`f` in `Φ` (continuous on `[0, 1]`, `f 0 = 0`, `0 ≤ f ≤ 1` on `[0, 1]`)
there is `n ≤ N` with `|f x - Pₙ x| < ε` for all `x ∈ [0, 1]`, where `Pₙ`
is the `n`-th partial sum. -/
def ScottishBookProblem159Claim : Prop :=
  ∃ a : ℕ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc 0 1) → f 0 = 0 →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc 0 1) →
      ∃ n : ℕ, n ≤ N ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
        dist (f x) (∑ k ∈ Finset.range (n + 1), a k * x ^ k) < ε

/--
Problem 159 is false: no such power series exists. The typescript's own
addendum Ad 159 states that in this formulation the answer is negative,
giving Sternbach's argument with the functions `sin²(2ⁿ π x)`, and records
Mazur's necessary and sufficient condition that, for an arbitrary set `Φ`
of this form, such a power series exists exactly when the functions of `Φ`
are equicontinuous (the equicontinuity criterion is recorded here in prose
and is not formalized). The typescript inequality is read with a universal
quantifier over `x`, as the Ad 159 argument uses the maximum over
`0 ≤ x ≤ 1`.
Source: S. Ruziewicz, Problem 159 of the Scottish Book; Ad 159 in the
typescript (Sternbach's negative argument; Mazur's equicontinuity criterion).
-/
theorem_wanted problem159Refuted : ¬ ScottishBookProblem159Claim

end MathlibExt.Analysis.ScottishBook159Wanted
