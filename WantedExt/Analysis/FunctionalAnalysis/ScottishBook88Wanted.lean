/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted

/-- Mazur's Problem 88 from the Scottish Book, in the form: if for every
bounded sequence `x` the inner series `∑ n, a (m + n) * x n` converge and
the outer series `∑ m, |∑ n, a (m + n) * x n|` converges, then
`∑ n, n * |a n|` converges. The inner series is stated via convergence of
partial sums, not absolute convergence, as in Mazur's original question. -/
def ScottishBookProblem88Claim : Prop :=
  ∀ a : ℕ → ℝ,
    (∀ x : ℕ → ℝ, (∀ n, |x n| ≤ 1) →
      ∃ L : ℕ → ℝ,
        (∀ m, Filter.Tendsto
          (fun N => ∑ n ∈ Finset.range N, a (m + n) * x n)
          Filter.atTop (nhds (L m))) ∧
        Summable (fun m => |L m|)) →
    Summable (fun n : ℕ => (n : ℝ) * |a n|)

/--
Mazur's Problem 88 is false: the hypothesis does not force
`∑ n, n * |a n|` to converge. Source: S. Mazur, Problem 88 of the Scottish
Book; negative solution as an immediate consequence of Peller (1982),
J. Operator Theory 7, 341-372, §5, via V. V. Peller, "On S. Mazur's Problems
8 and 88 from the Scottish Book", arXiv:math/0703716: a Hankel matrix in the
injective tensor product need not have finite sum of moduli of its entries.
-/
theorem_wanted mazur88_refuted : ¬ ScottishBookProblem88Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted
