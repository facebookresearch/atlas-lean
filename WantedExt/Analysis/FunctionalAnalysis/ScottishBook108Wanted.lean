/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted

/-- **Schauder basis.** A sequence $(e_n)_{n \ge 0}$ in a real normed space $E$ is a Schauder
basis when for every $x \in E$ there is exactly one sequence of real numbers $(a_n)_{n \ge 0}$
such that the partial sums $\sum_{i < N} a_i e_i$ converge to $x$ as $N \to \infty$. -/
def IsSchauderBasis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℕ → E) : Prop :=
  ∀ x : E, ∃! a : ℕ → ℝ,
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, a i • e i)
      Filter.atTop (nhds x)

/--
**Krein's theorem on bases in dense sets.** Let $E$ be a real Banach space that has a Schauder
basis. Then for every dense subset $H \subseteq E$ there is a Schauder basis $(e_n)_{n \ge 0}$ of
$E$ with $e_n \in H$ for all $n$, and likewise for every dense linear subspace $S \subseteq E$
there is a Schauder basis $(e_n)_{n \ge 0}$ of $E$ with $e_n \in S$ for all $n$.

Source: S. Banach,
S. Mazur, S. Ulam, Problem 108 of the Scottish Book; affirmative answer
(Krein), typescript addendum Ad 108.
-/
theorem_wanted krein_basis_in_dense_set :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      (∃ e : ℕ → E, IsSchauderBasis e) →
      (∀ H : Set E, Dense H →
        ∃ e : ℕ → E, IsSchauderBasis e ∧ ∀ n, e n ∈ H) ∧
      (∀ S : Submodule ℝ E, Dense (S : Set E) →
        ∃ e : ℕ → E, IsSchauderBasis e ∧ ∀ n, e n ∈ S)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted
