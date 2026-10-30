/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counting condition forcing prime-power element orders (Kourovka Notebook Problem 18.112)

Kourovka Notebook, Archive of Solved Problems, Problem 18.112 (W. J. Shi): is it true that the
orders of all elements of a finite group `G` are powers of primes if, for every divisor `d > 1` of
`|G|` and for every subgroup `H` of `G` of order coprime to `d`, the order `|H|` divides the number
of elements of `G` of order `d`? (The converse is true (Shi).)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.112 (W. J.
Shi). UnsolvedMath record UM-00701540 (`KOU-18.112`), dataset ulamai/UnsolvedMath v1.8.0.

Element orders are `orderOf`; the identity has order `1 = p⁰`, so the conclusion is stated for
non-identity elements (`IsPrimePow` excludes `1`).
-/

/-- Kourovka 18.112 (W. J. Shi): if a finite group `G` has the property that, for every divisor
`d > 1` of `|G|` and every subgroup `H` of order coprime to `d`, `|H|` divides the number of
elements of order `d`, then every element of `G` has prime-power order (the identity having order
`1 = p⁰`). -/
def elementOrderCountPrimePowerOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ d : ℕ, 1 < d → d ∣ Nat.card G → ∀ H : Subgroup G, Nat.Coprime (Nat.card H) d →
      Nat.card H ∣ Nat.card {g : G // orderOf g = d}) →
    ∀ g : G, g ≠ 1 → IsPrimePow (orderOf g)

/--
Resolved true: the Kourovka Archive answers 18.112 "Yes, it is true", citing Buturlakin, Shen and
Shi (2017): if for every divisor `d > 1` of `|G|` and every subgroup `H` of order coprime to `d` the
order `|H|` divides the number of elements of order `d`, then every element of `G` has prime-power
order. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.112
(W. J. Shi); resolution: A. A. Buturlakin, R. Shen and W. Shi, Siberian Math. J. 58 (2017), 405-407,
Kourovka Archive, Problem 18.112 (Yes, it is true).
-/
public theorem_wanted elementOrderCountPrimePowerOrders_holds : elementOrderCountPrimePowerOrders

end MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted
