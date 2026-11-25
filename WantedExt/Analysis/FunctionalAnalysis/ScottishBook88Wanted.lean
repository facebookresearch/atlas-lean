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

/-- **Scottish Book Problem 88 (Mazur).** The claim that every real sequence $(a_n)_{n \ge 0}$
with the following property satisfies $\sum_n n |a_n| < \infty$: for every real sequence
$(x_n)_{n \ge 0}$ with $|x_n| \le 1$ for all $n$, each series $\sum_n a_{m+n} x_n$ with $m \ge 0$
converges, as the limit of its partial sums, to some $L_m$, and $\sum_m |L_m| < \infty$.

The inner series is required to converge as a limit of partial sums, not absolutely, as in
Mazur's original question. -/
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
**Mazur's Scottish Book Problem 88 fails.** The Scottish Book Problem 88 claim is false: there is
a real sequence $(a_n)_{n \ge 0}$ such that for every real sequence $(x_n)_{n \ge 0}$ with
$|x_n| \le 1$ for all $n$, each series $\sum_n a_{m+n} x_n$ with $m \ge 0$ converges, as the
limit of its partial sums, to some $L_m$, and $\sum_m |L_m| < \infty$, but $\sum_n n |a_n|$
diverges.

Source: S. Mazur, Problem 88 of the Scottish
Book; negative solution as an immediate consequence of Peller (1982),
J. Operator Theory 7, 341-372, §5, via V. V. Peller, "On S. Mazur's Problems
8 and 88 from the Scottish Book", arXiv:math/0703716: a Hankel matrix in the
injective tensor product need not have finite sum of moduli of its entries.
-/
theorem_wanted mazur88_refuted : ¬ ScottishBookProblem88Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted
