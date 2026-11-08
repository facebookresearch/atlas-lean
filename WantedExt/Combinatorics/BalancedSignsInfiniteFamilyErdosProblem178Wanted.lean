/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Balanced signs on an infinite family of sequences (Erdős Problem 178)

Erdős Problem 178: let `A₁, A₂, …` be infinite sets of integers, `Aᵢ = {a_{i1} < a_{i2} < ⋯}`. Is
there `f : ℕ → {-1, 1}` with `max_{m, 1 ≤ i ≤ d} |∑_{j ≤ m} f(a_{ij})| ≪_d 1` for all `d ≥ 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs

@[expose] public section

namespace MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #178, https://www.erdosproblems.com/178 (status PROVED
(LEAN)). UnsolvedMath record UM-30006751 (`EP-178`), dataset ulamai/UnsolvedMath v1.8.0.

The sets are subsets of `ℕ` (the domain of `f`), given by strictly increasing enumerations `a i`;
indices start at `0`, so `1 ≤ i ≤ d` becomes `i < d`. `≪_d 1` is a bound `C` depending only on `d`,
uniform in `m`. Compared with the formal-conjectures statement `ErdosProblems/178.lean` (equivalent;
no code imported).
-/

/-- Erdős Problem 178: for every sequence of infinite sets `Aᵢ = {a i 0 < a i 1 < ⋯} ⊆ ℕ` there is
`f : ℕ → {-1, 1}` such that for every `d` the partial sums `∑_{j < m} f (a i j)`, `i < d`, `m ∈ ℕ`,
are bounded by a constant depending only on `d`. -/
def boundedDiscrepancyInfiniteFamily : Prop :=
  ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ i < d, ∀ m : ℕ, |∑ j ∈ Finset.range m, f (a i j)| ≤ C

/--
Resolved true: Beck proved that such a colouring `f` exists; he later showed that the bound can be
taken `≪ d^{4 + ε}`. erdosproblems.com/178 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #178, https://www.erdosproblems.com/178 (status PROVED (LEAN)); resolution: J.
Beck, Balancing families of integer sequences, Combinatorica 1 (1981), 209-216,
erdosproblems.com/178: solved by Beck [Be81]; Beck (2017) improved the bound to d^{4+ε},
https://doi.org/10.1007/BF02579326.
-/
public theorem_wanted boundedDiscrepancyInfiniteFamily_holds : boundedDiscrepancyInfiniteFamily

end MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178Wanted
