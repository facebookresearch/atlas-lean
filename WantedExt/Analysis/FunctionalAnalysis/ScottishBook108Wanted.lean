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

/-- A Schauder basis of a real Banach space: every vector has a unique
expansion as a convergent series in the basis vectors, in order. -/
def IsSchauderBasis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℕ → E) : Prop :=
  ∀ x : E, ∃! a : ℕ → ℝ,
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, a i • e i)
      Filter.atTop (nhds x)

/--
Krein's affirmative answer to Banach-Mazur-Ulam Problem 108: in a Banach
space with a (Schauder) basis, (1) for every everywhere-dense set `H` there
is a basis whose terms lie in `H`, and (2) the same holds when `H` is a
linear subspace, here encoded by a dense submodule. Source: S. Banach,
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
