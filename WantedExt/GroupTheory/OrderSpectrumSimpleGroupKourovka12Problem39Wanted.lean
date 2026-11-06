/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recognition of finite simple groups by order and element orders (Kourovka Notebook Problem 12.39)

Kourovka Notebook, Archive of Solved Problems, Problem 12.39 (W. J. Shi; A. S. Kondratiev): must a
finite group and a finite simple group be isomorphic if they have equal orders and the same set of
orders of elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.OrderSpectrumSimpleGroupKourovka12Problem39Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.39 (W. J.
Shi; A. S. Kondratiev). UnsolvedMath record UM-00700858 (`KOU-12.39`), dataset ulamai/UnsolvedMath
v1.8.0.

Simple is `IsSimpleGroup`, which includes the cyclic groups of prime order (where the statement is
immediate); the set of element orders is the range of `orderOf`.
-/

/-- **Set of element orders (Kourovka 12.39).** For a group $G$, the set of natural numbers that
occur as the order of some element of $G$, where an element of infinite order is counted as
having order $0$. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **Shi's conjecture on recognition by order and element orders (Kourovka 12.39).** The
statement that for every finite group $G$ and every finite simple group $S$, if $G$ and $S$ have
the same order and the same set of element orders, then $G$ is isomorphic to $S$. -/
def simpleGroupRecognizedByOrderAndSpectrum : Prop :=
  ∀ (G S : Type) [Group G] [Finite G] [Group S] [Finite S], IsSimpleGroup S →
    Nat.card G = Nat.card S → elementOrders G = elementOrders S → Nonempty (G ≃* S)

/--
**Finite simple groups are recognized by order and element orders.** For every finite group $G$
and every finite simple group $S$, if $G$ and $S$ have the same order and the same set of element
orders, then $G$ is isomorphic to $S$. That is, Shi's conjecture (Kourovka Problem 12.39) holds.

Here a simple group may be cyclic of prime order. The Kourovka Archive records the answer "Yes,
they must", proved by Xu and Shi and by Vasil'ev, Grechkoseeva and Mazurov.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.39
(W. J. Shi; A. S. Kondratiev); resolution: M. C. Xu and W. J. Shi, Algebra Colloq. 10 (2003),
427-443; A. V. Vasil'ev, M. A. Grechkoseeva and V. D. Mazurov, Algebra Logic 48 (2009), 385-409,
Kourovka Archive, Problem 12.39: Yes, they must.
-/
public theorem_wanted simpleGroupRecognizedByOrderAndSpectrum_holds :
    simpleGroupRecognizedByOrderAndSpectrum

end MathlibExt.GroupTheory.OrderSpectrumSimpleGroupKourovka12Problem39Wanted
