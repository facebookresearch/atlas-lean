/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with countably infinitely many right orders (Kourovka Notebook Problem 16.51)

Kourovka Notebook, Problem 16.51 (V. M. Kopytov, N. Ya. Medvedev): do there exist groups that can be
right-ordered in infinitely countably many ways?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Countable

@[expose] public section

namespace MathlibExt.GroupTheory.CountablyManyRightOrdersKourovka16Problem51Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.51 (V. M. Kopytov, N. Ya. Medvedev).
UnsolvedMath record UM-00701243 (`KOU-16.51`), dataset ulamai/UnsolvedMath v1.8.0.

The right orders of `G` are the linear orders (as relations) invariant under right multiplication,
and the question asks whether this set can be countably infinite.
-/

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- Kourovka 16.51 (V. M. Kopytov, N. Ya. Medvedev): some group has countably infinitely many right
orders. -/
def existsCountablyInfinitelyRightOrderable : Prop :=
  ∃ (G : Type) (_ : Group G), (rightOrders G).Countable ∧ (rightOrders G).Infinite

/--
Resolved false: Linnell (Theorem 1.3; also Clay, Corollary 3.10) proves that the set of left orders
of a group is either finite or uncountable, extending Zenkov's theorem for locally indicable groups;
left and right orders correspond through `a ≤' b ↔ b⁻¹ ≤ a⁻¹`. The Kourovka Notebook (21st issue)
answers 16.51 "No, there are no such groups", citing Clay, Navas and Rivas, and Linnell. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.51 (V. M. Kopytov, N. Ya. Medvedev); resolution: P. A.
Linnell, Bull. London Math. Soc. 43 (2011), 200-202; A. Clay, preprint, arXiv:0909.0273 (2009); A.
Navas and C. Rivas, Algebr. Geom. Topol. 9 (2009), 2079-2100, Linnell, Theorem 1.3 (no group can be
left-ordered in a countably infinite number of ways), based on A. V. Zenkov (1997, locally indicable
groups); Clay, Corollary 3.10 (the set of left orderings of any group is finite or uncountable); the
Kourovka Notebook (21st issue) marks 16.51 solved (No, there are no such groups),
https://arxiv.org/abs/0909.0273.
-/
public theorem_wanted existsCountablyInfinitelyRightOrderable_refuted :
    ¬ existsCountablyInfinitelyRightOrderable

end MathlibExt.GroupTheory.CountablyManyRightOrdersKourovka16Problem51Wanted
