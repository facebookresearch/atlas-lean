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

/-- **Shi's question on element-order counts (Kourovka 18.112).** The proposition that if a
finite group $G$ has the property that, for every divisor $d > 1$ of $|G|$ and every subgroup $H$
of $G$ whose order is coprime to $d$, $|H|$ divides the number of elements of $G$ of order $d$,
then every non-identity element of $G$ has prime-power order. -/
def elementOrderCountPrimePowerOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ d : ℕ, 1 < d → d ∣ Nat.card G → ∀ H : Subgroup G, Nat.Coprime (Nat.card H) d →
      Nat.card H ∣ Nat.card {g : G // orderOf g = d}) →
    ∀ g : G, g ≠ 1 → IsPrimePow (orderOf g)

/--
**Counting elements of each order forces prime-power orders.** Let $G$ be a finite group such
that for every divisor $d > 1$ of $|G|$ and every subgroup $H$ of $G$ whose order is coprime to
$d$, the order $|H|$ divides the number of elements of $G$ of order $d$. Then every non-identity
element of $G$ has prime-power order.

Buturlakin, Shen and Shi proved this in 2017, answering Kourovka Problem 18.112 (W. J. Shi); the
Kourovka Archive answers 18.112 "Yes, it is true".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.112
(W. J. Shi); resolution: A. A. Buturlakin, R. Shen and W. Shi, Siberian Math. J. 58 (2017), 405-407,
Kourovka Archive, Problem 18.112 (Yes, it is true).
-/
public theorem_wanted elementOrderCountPrimePowerOrders_holds : elementOrderCountPrimePowerOrders

end MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted
