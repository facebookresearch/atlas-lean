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

/-- The set of orders of elements of `G`. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- Kourovka 12.39 (W. J. Shi): a finite group and a finite simple group with equal orders and
the same set of element orders are isomorphic. -/
def simpleGroupRecognizedByOrderAndSpectrum : Prop :=
  ∀ (G S : Type) [Group G] [Finite G] [Group S] [Finite S], IsSimpleGroup S →
    Nat.card G = Nat.card S → elementOrders G = elementOrders S → Nonempty (G ≃* S)

/--
Resolved true: the Kourovka Archive answers 12.39 "Yes, they must" (Shi's conjecture), proved by Xu
and Shi (Algebra Colloq. 10 (2003)) and Vasil'ev, Grechkoseeva and Mazurov (Algebra Logic 48
(2009)). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.39
(W. J. Shi; A. S. Kondratiev); resolution: M. C. Xu and W. J. Shi, Algebra Colloq. 10 (2003),
427-443; A. V. Vasil'ev, M. A. Grechkoseeva and V. D. Mazurov, Algebra Logic 48 (2009), 385-409,
Kourovka Archive, Problem 12.39: Yes, they must.
-/
public theorem_wanted simpleGroupRecognizedByOrderAndSpectrum_holds :
    simpleGroupRecognizedByOrderAndSpectrum

end MathlibExt.GroupTheory.OrderSpectrumSimpleGroupKourovka12Problem39Wanted
