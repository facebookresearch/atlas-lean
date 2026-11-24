/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook8Wanted

/-- **The claim of Scottish Book Problem 8.** This is the statement, asked about in form (b) of
Mazur's Problem 8 in the Scottish Book typescript, that every convergent sequence
$(z_n)_{n \ge 0}$ of real numbers can be written as
$z_n = \frac{1}{n+1} \sum_{k=0}^{n} x_k y_{n-k}$ for all $n \ge 0$, where $(x_n)_{n \ge 0}$
and $(y_n)_{n \ge 0}$ are convergent sequences of real numbers.

Indices are shifted to start at $0$. -/
def ScottishBookProblem8Claim : Prop :=
  ∀ (z : ℕ → ℝ), (∃ L, Filter.Tendsto z Filter.atTop (nhds L)) →
    ∃ (x y : ℕ → ℝ), (∃ Lx, Filter.Tendsto x Filter.atTop (nhds Lx)) ∧
      (∃ Ly, Filter.Tendsto y Filter.atTop (nhds Ly)) ∧
      ∀ n, z n = (∑ k ∈ Finset.range (n + 1), x k * y (n - k)) / (n + 1 : ℝ)

/--
**Mazur's Problem 8 has a negative answer.** There is a convergent sequence
$(z_n)_{n \ge 0}$ of real numbers that cannot be written as
$z_n = \frac{1}{n+1} \sum_{k=0}^{n} x_k y_{n-k}$ for all $n \ge 0$ with convergent sequences
$(x_n)_{n \ge 0}$ and $(y_n)_{n \ge 0}$ of real numbers. That is, the claim of Scottish Book
Problem 8 is false.

Source: S. Mazur, Problem 8 of the Scottish Book; negative
solution by V. V. Peller, "On S. Mazur's Problems 8 and 88 from the Scottish
Book", arXiv:math/0703716, building on Peller, J. Operator Theory 7 (1982)
341-372; independently Kwapien-Pelczynski and Eggermont-Leung, Proc. Amer.
Math. Soc. 96 (1986) 269-274.
-/
theorem_wanted mazur8CauchyProduct_refuted : ¬ ScottishBookProblem8Claim

end MathlibExt.Analysis.ScottishBook8Wanted
