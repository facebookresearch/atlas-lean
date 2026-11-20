/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite simple groups of a given exponent (Kourovka Notebook Problem 1.21)

Kourovka Notebook, Archive of Solved Problems, Problem 1.21 (M. I. Kargapolov): are there only
finitely many finite simple groups of a given exponent `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteSimpleGroupsBoundedExponentKourovka1Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.21 (M. I.
Kargapolov). UnsolvedMath record UM-00700017 (`KOU-1.21`), dataset ulamai/UnsolvedMath v1.8.0.

"Finitely many" is stated as a bound on the orders, which is equivalent to finitely many isomorphism
classes. Exponent dividing `n` (the law `gⁿ = 1`) is used instead of exponent exactly `n`; it
implies the exact form and is equivalent to it, as `n` has finitely many divisors. `n ≥ 1` is
required because the law `g⁰ = 1` holds in every group.
-/

/-- Kourovka 1.21 (M. I. Kargapolov): for every `n ≥ 1` there are only finitely many finite simple
groups of exponent dividing `n`, in the form: their orders are bounded. -/
def finitelyManyFiniteSimpleGroupsOfExponent : Prop :=
  ∀ n : ℕ, 0 < n → ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∀ g : G, g ^ n = 1) → Nat.card G ≤ N

/--
Resolved true: the Kourovka Archive answers 1.21 "Yes, modulo CFSG", citing Jones; with the
classification of finite simple groups, only finitely many finite simple groups satisfy the law `gⁿ
= 1` for a given `n ≥ 1`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 1.21 (M. I. Kargapolov); resolution: G. A. Jones, J. Austral. Math. Soc. 17 (1974), 162-173,
Kourovka Archive, Problem 1.21 (Yes, modulo the classification of finite simple groups).
-/
public theorem_wanted finitelyManyFiniteSimpleGroupsOfExponent_holds :
    finitelyManyFiniteSimpleGroupsOfExponent

end MathlibExt.GroupTheory.FiniteSimpleGroupsBoundedExponentKourovka1Problem21Wanted
