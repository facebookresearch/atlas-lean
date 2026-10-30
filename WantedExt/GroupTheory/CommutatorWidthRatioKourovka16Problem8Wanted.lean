/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Commutator width of the derived subgroup relative to the order (Kourovka Notebook Problem 16.8)

Kourovka Notebook, Archive of Solved Problems, Problem 16.8 (V. G. Bardakov): the width `w(G')` of
the derived subgroup `G'` of a finite non-abelian group `G` is the smallest positive integer `m`
such that every element of `G'` is a product of `≤ m` commutators. Is it true that the maximum value
of the ratio `w(G')/|G|` is `1/6` (attained at the symmetric group `S₃`)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.8 (V. G.
Bardakov). UnsolvedMath record UM-00701200 (`KOU-16.8`), dataset ulamai/UnsolvedMath v1.8.0.

Commutators are `a b a⁻¹ b⁻¹` (the same set as for `a⁻¹ b⁻¹ a b`), `w(G')` is the infimum of the
admissible positive `m`, and the target is the problem's claim: `w(G')/|G| ≤ 1/6` for every finite
non-abelian `G`, with equality for `S₃ = Equiv.Perm (Fin 3)`.
-/

/-- `g` is a product of at most `m` commutators `a b a⁻¹ b⁻¹`. -/
def IsProductOfCommutators {G : Type*} [Group G] (m : ℕ) (g : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ m ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = g

/-- The width `w(G')` of the derived subgroup: the least positive `m` such that every element of
`G'` is a product of at most `m` commutators. -/
noncomputable def commutatorWidth (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ g ∈ commutator G, IsProductOfCommutators m g}

/-- Kourovka 16.8 (V. G. Bardakov): the maximum of `w(G') / |G|` over finite non-abelian groups `G`
is `1/6`, attained at the symmetric group `S₃`. -/
def maxCommutatorWidthRatioIsOneSixth : Prop :=
  (∀ (G : Type) [Group G] [Finite G], (∃ a b : G, a * b ≠ b * a) →
      (commutatorWidth G : ℚ) / Nat.card G ≤ 1 / 6) ∧
    (commutatorWidth (Equiv.Perm (Fin 3)) : ℚ) / Nat.card (Equiv.Perm (Fin 3)) = 1 / 6

/--
Resolved true: the Kourovka Archive answers 16.8 "Yes, it is", citing Bonner (2008): `w(G') ≤ |G|/6`
for every finite non-abelian group `G`, and `S₃`, whose derived subgroup `A₃` consists of
commutators, attains `1/6`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 16.8 (V. G. Bardakov); resolution: T. Bonner, J. Algebra 320 (2008), 3165-3171,
Kourovka Archive, Problem 16.8 (Yes, it is).
-/
public theorem_wanted maxCommutatorWidthRatioIsOneSixth_holds : maxCommutatorWidthRatioIsOneSixth

end MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted
