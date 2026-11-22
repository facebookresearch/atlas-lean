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

/-- **Products of a bounded number of commutators.** For a group $G$, a natural number $m$ and
$g \in G$, $g$ is a product of at most $m$ commutators when there are $k \le m$ and
$a_1, b_1, \dots, a_k, b_k \in G$ with $g = [a_1, b_1] \cdots [a_k, b_k]$, where
$[a, b] = aba^{-1}b^{-1}$; for $k = 0$ the empty product is the identity. -/
def IsProductOfCommutators {G : Type*} [Group G] (m : ℕ) (g : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ m ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = g

/-- **Commutator width of the derived subgroup.** For a group $G$ with derived subgroup $G'$, the
commutator width $w(G')$ is the least positive integer $m$ such that every element of $G'$ is a
product of at most $m$ commutators $aba^{-1}b^{-1}$ with $a, b \in G$; it is $0$ when no such $m$
exists. -/
noncomputable def commutatorWidth (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ g ∈ commutator G, IsProductOfCommutators m g}

/-- **Bardakov's commutator width ratio claim (Kourovka 16.8).** The proposition that for every
finite non-abelian group $G$ the commutator width $w(G')$ of its derived subgroup $G'$ satisfies
$w(G')/|G| \le 1/6$, and that for the symmetric group $S_3$ equality holds:
$w(S_3')/|S_3| = 1/6$. -/
def maxCommutatorWidthRatioIsOneSixth : Prop :=
  (∀ (G : Type) [Group G] [Finite G], (∃ a b : G, a * b ≠ b * a) →
      (commutatorWidth G : ℚ) / Nat.card G ≤ 1 / 6) ∧
    (commutatorWidth (Equiv.Perm (Fin 3)) : ℚ) / Nat.card (Equiv.Perm (Fin 3)) = 1 / 6

/-- **The maximal commutator width ratio is one sixth.** For every finite non-abelian group $G$,
the commutator width $w(G')$ of its derived subgroup satisfies $w(G')/|G| \le 1/6$, and for the
symmetric group $S_3$ equality holds, $w(S_3')/|S_3| = 1/6$; so Kourovka Problem 16.8 has a
positive answer.

The Kourovka Archive answers 16.8 "Yes, it is", citing Bonner (2008) for the bound; $S_3$ attains
it because its derived subgroup $A_3$ consists of commutators.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 16.8 (V. G. Bardakov); resolution: T. Bonner, J. Algebra 320 (2008), 3165-3171,
Kourovka Archive, Problem 16.8 (Yes, it is).
-/
public theorem_wanted maxCommutatorWidthRatioIsOneSixth_holds : maxCommutatorWidthRatioIsOneSixth

end MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted
