/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Algebra.KourovkaProblem2143SolvableElementOrdersWanted


/-!
# Kourovka Notebook Problem 21.43

Clause list for the conjecture (hypotheses, side conditions, quantifier domains):
1. `G` is a finite group — quantifier domain `Type*` with `[Group G]` and `[Finite G]`.
2. `k` is a fixed positive integer — quantifier domain `ℕ` with side condition `0 < k`.
3. At least half of the elements of `G` have order exactly `k` —
   `2 * Nat.card { g : G // orderOf g = k } ≥ Nat.card G`.
4. Conclusion: `G` is solvable — `Group.IsSolvable G`.

The `Prop` below is the universal implication (1)–(3) ⇒ (4) over `G` and `k`.
-/

/-- Kourovka Notebook Problem 21.43 [KOU-21.43] (New Problems, 21st issue, 2026):
For a fixed positive integer `k`, if at least half of the elements of a finite
group `G` have order `k`, then `G` is solvable. -/
def conjecture : Prop :=
  ∀ (G : Type*) [Group G] [Finite G] (k : ℕ), 0 < k →
    2 * Nat.card { g : G // orderOf g = k } ≥ Nat.card G → Group.IsSolvable G

/--
Resolved false: Refuted: in A₅^N the number of elements of order 30 is 60^N − 45^N − 40^N − 36^N
+ 25^N + 21^N + 16^N − 1, more than half of 60^N for N ≥ 5, although A₅^N is not solvable (L.
Tae Young, letter of 9 January 2026, recorded in the Kourovka Notebook, arXiv:1401.0300v49,
which marks Problem 21.43 solved). R. McCulloch and L. Tae Young (arXiv:2602.19340, 2026) study
for which k the conjecture holds. Source: R. McCulloch and L. Tae Young, Finite groups with many
elements of the same order, arXiv:2602.19340 (2026), https://arxiv.org/abs/2602.19340; E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (20 October 2026), Problem 21.43, https://arxiv.org/abs/1401.0300v49.
Moved from `OpenConjectures/Algebra/KourovkaProblem2143SolvableElementOrders`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.KourovkaProblem2143SolvableElementOrdersWanted
