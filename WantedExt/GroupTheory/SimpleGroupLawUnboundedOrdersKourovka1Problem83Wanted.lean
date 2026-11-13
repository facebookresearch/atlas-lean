/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with an identity and unbounded element orders (Kourovka Notebook Problem 1.83)

Kourovka Notebook, Archive of Solved Problems, Problem 1.83 (A. L. Shmel'kin): does there exist a
simple group, the orders of whose elements are unbounded, in which a non-trivial identity relation
holds?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupLawUnboundedOrdersKourovka1Problem83Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.83 (A. L.
Shmel'kin). UnsolvedMath record UM-00700072 (`KOU-1.83`), dataset ulamai/UnsolvedMath v1.8.0.

"The orders of the elements are unbounded" is read as the negation of bounded orders: no `N ≥ 1` has
`g ^ N = 1` for all `g` (this also covers elements of infinite order). A non-trivial identity is a
word `w ≠ 1` in `x₀, x₁, …` that evaluates to `1` under every assignment.
-/

/-- Kourovka 1.83 (A. L. Shmel'kin): some simple group whose element orders are unbounded (no
`N ≥ 1` with `g ^ N = 1` for all `g`) satisfies a nontrivial identity `w ≠ 1`, a word in the
variables `x₀, x₁, …` that evaluates to `1` under every assignment. -/
def simpleGroupWithLawUnboundedOrders : Prop :=
  ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ (∀ N : ℕ, 0 < N → ∃ g : G, g ^ N ≠ 1) ∧
    ∃ w : FreeGroup ℕ, w ≠ 1 ∧ ∀ f : ℕ → G, FreeGroup.lift f w = 1

/--
Resolved true: the Kourovka Archive answers "Yes, such groups do exist", citing Atabekyan (VINITI
deposit, 1986): some simple group whose element orders are unbounded satisfies a non-trivial
identity. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.83
(A. L. Shmel'kin); resolution: V. S. Atabekyan, Dep. no. 5381-V86, VINITI, Moscow, 1986 (Russian),
Kourovka Archive, Problem 1.83 ("Yes, such groups do exist").
-/
public theorem_wanted simpleGroupWithLawUnboundedOrders_holds : simpleGroupWithLawUnboundedOrders

end MathlibExt.GroupTheory.SimpleGroupLawUnboundedOrdersKourovka1Problem83Wanted
