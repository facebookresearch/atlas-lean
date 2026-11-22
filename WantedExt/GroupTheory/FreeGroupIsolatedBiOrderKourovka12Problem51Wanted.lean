/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Isolated bi-orders of free groups (Kourovka Notebook Problem 12.51)

Kourovka Notebook, Problem 12.51 (S. McCleary), marked solved in the 21st issue: does the free group
`F_η` (`1 < η < ∞`) have a finite subset `S` for which there is a unique total order of `F_η` making
all elements of `S` positive? Equivalently, does the free representable `l`-group of rank `η` have a
basic element?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupIsolatedBiOrderKourovka12Problem51Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.51 (S. McCleary). UnsolvedMath record
UM-00700870 (`KOU-12.51`), dataset ulamai/UnsolvedMath v1.8.0.

The total orders are bi-invariant (two-sided) orders, as the equivalent formulation with the free
representable `l`-group shows (the right-order analogue is mentioned separately in the problem):
strict total orders `r` with `r a b → r (c a d) (c b d)`. Rank 1 is excluded as in the problem (`ℤ`
has two bi-orders and `S = {x}` singles one out). The target is stated for some rank `n ≥ 2` (the
strongest true form, existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its
refutation asserts that no `Fₙ`, `2 ≤ n < ∞`, has an isolated bi-order: stronger than the source's
negative answer, which needs one rank, and what Muliarchyk proves (`Fₙ` is a free product of `n ≥ 2`
copies of `ℤ`).
-/

/-- `r` is a bi-invariant (strict) total order on the group `G`. -/
def IsBiOrder {G : Type*} [Group G] (r : G → G → Prop) : Prop :=
  IsStrictTotalOrder G r ∧ ∀ a b c d : G, r a b → r (c * a * d) (c * b * d)

/-- Kourovka 12.51 (S. McCleary), stated for some finite rank `n ≥ 2`: the free group `Fₙ` has a
finite subset `S` such that exactly one bi-invariant total order of `Fₙ` makes every element of
`S` positive (an isolated point of the space of bi-orders). -/
def freeGroupHasIsolatedBiOrder : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ S : Finset (FreeGroup (Fin n)),
    ∃! r : FreeGroup (Fin n) → FreeGroup (Fin n) → Prop, IsBiOrder r ∧ ∀ s ∈ S, r 1 s

/--
Resolved false: the Kourovka Notebook (21st issue) marks 12.51 solved, "No, it does not". Muliarchyk
(arXiv:2403.14779) proves that a free product of bi-ordered groups admits no isolated bi-ordering,
so no free group `ℤ ∗ ⋯ ∗ ℤ` of finite rank `n ≥ 2` has a finite set `S` singling out one bi-order
(see also Dovhyi and Muliarchyk, Groups Geom. Dyn. 17 (2023)). Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 12.51 (S. McCleary); resolution: K. Muliarchyk, Free products of
bi-orderable groups, preprint (2024), arXiv:2403.14779; S. Dovhyi and K. Muliarchyk, Groups Geom.
Dyn. 17 (2023), 613-632, Muliarchyk, main theorem: a free product of bi-ordered groups admits no
isolated bi-ordering; the Kourovka Notebook (21st issue) marks 12.51 solved,
https://arxiv.org/abs/2403.14779.
-/
public theorem_wanted freeGroupHasIsolatedBiOrder_refuted : ¬ freeGroupHasIsolatedBiOrder

end MathlibExt.GroupTheory.FreeGroupIsolatedBiOrderKourovka12Problem51Wanted
