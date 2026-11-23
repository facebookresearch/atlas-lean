/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local convexity of the growth function (Kourovka Notebook Problem 5.2)

Kourovka Notebook, Archive of Solved Problems, Problem 5.2 (V. V. Belyaev, N. F. Sesekin): is it
true that the growth function f of any infinite finitely generated group satisfies f(n) ≤ (f(n-1) +
f(n+1))/2 for all sufficiently large n (for a fixed finite system of generators)?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.GroupGrowth

@[expose] public section

namespace MathlibExt.GroupTheory.GrowthFunctionLocalConvexityKourovka5Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.2 (V. V.
Belyaev, N. F. Sesekin). UnsolvedMath record UM-00700286 (`KOU-5.2`), dataset ulamai/UnsolvedMath
v1.8.0.

The growth function of a finite generating family `P : Group.Generators G ι` is MathlibExt's
`Group.Generators.growth`: the number of elements of word length at most `n` over the generators and
their inverses. The inequality is stated without division as `2 f(n) ≤ f(n - 1) + f(n + 1)`.
-/

/-- Kourovka 5.2 (V. V. Belyaev, N. F. Sesekin): the growth function `f(n)` of an infinite
finitely generated group `G` with respect to a fixed finite generating family `P` (the number of
elements of word length at most `n`, `Group.Generators.growth`) satisfies
`f(n) ≤ (f(n - 1) + f(n + 1)) / 2` for all sufficiently large `n`. -/
def growthFunctionLocallyConvex : Prop :=
  ∀ (G : Type) [Group G] [Infinite G] (ι : Type) [Finite ι] (P : Group.Generators G ι),
    ∃ N : ℕ, ∀ n ≥ N, 2 * P.growth n ≤ P.growth (n - 1) + P.growth (n + 1)

/--
Resolved false: de la Harpe and Grigorchuk (Algebra and Logic 37 (1998), 353-356, abstract) refute
the conjecture with the infinite group `⟨a, b | a³ = b³ = (ab)³ = 1⟩`, whose growth function
violates `σ(n) ≤ (σ(n - 1) + σ(n + 1)) / 2` for arbitrarily large `n`; the Kourovka Archive answers
5.2 "No". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.2
(V. V. Belyaev, N. F. Sesekin); resolution: P. de la Harpe and R. I. Grigorchuk, Local convexity of
the growth function of finitely generated groups and question 5.2 in the Kourovka notebook, Algebra
and Logic 37 (1998), 353-356, abstract: using the group ⟨a, b | a³ = b³ = (ab)³ = 1⟩ the authors
refute the conjecture that the growth function σ(n) of a finitely generated group satisfies σ(n) ≤
(σ(n-1) + σ(n+1))/2 for all sufficiently large n; Kourovka Archive, Problem 5.2: No,
https://doi.org/10.1007/BF02671688.
-/
public theorem_wanted growthFunctionLocallyConvex_refuted : ¬ growthFunctionLocallyConvex

end MathlibExt.GroupTheory.GrowthFunctionLocalConvexityKourovka5Problem2Wanted
