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

/-- Mazur's Problem 8 from the Scottish Book, in the form (b) of the
typescript: given any convergent sequence `z`, do there exist convergent
sequences `x` and `y` with `z n = (x 0 * y n + ... + x n * y 0) / (n + 1)`
for every `n` (indices shifted to start at `0`)? -/
def ScottishBookProblem8Claim : Prop :=
  ∀ (z : ℕ → ℝ), (∃ L, Filter.Tendsto z Filter.atTop (nhds L)) →
    ∃ (x y : ℕ → ℝ), (∃ Lx, Filter.Tendsto x Filter.atTop (nhds Lx)) ∧
      (∃ Ly, Filter.Tendsto y Filter.atTop (nhds Ly)) ∧
      ∀ n, z n = (∑ k ∈ Finset.range (n + 1), x k * y (n - k)) / (n + 1 : ℝ)

/--
Problem 8 is false: there is a convergent sequence not representable in the
form (b) above. Source: S. Mazur, Problem 8 of the Scottish Book; negative
solution by V. V. Peller, "On S. Mazur's Problems 8 and 88 from the Scottish
Book", arXiv:math/0703716, building on Peller, J. Operator Theory 7 (1982)
341-372; independently Kwapien-Pelczynski and Eggermont-Leung, Proc. Amer.
Math. Soc. 96 (1986) 269-274.
-/
theorem_wanted mazur8CauchyProduct_refuted : ¬ ScottishBookProblem8Claim

end MathlibExt.Analysis.ScottishBook8Wanted
