/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wall's bound on the number of maximal subgroups (Kourovka Notebook Problem 7.17)

Kourovka Notebook, Archive of Solved Problems, Problem 7.17 (R. Griess): is the number of maximal
subgroups of the finite group `G` at most `|G| - 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalSubgroupCountWallKourovka7Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.17 (R.
Griess). UnsolvedMath record UM-00700418 (`KOU-7.17`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are the coatoms of the subgroup lattice (`IsCoatom`); the trivial group has none,
so the bound `|G| - 1` in natural-number subtraction is the same as "fewer than `|G|`" (G. E. Wall's
conjecture of 1961).
-/

/-- Kourovka 7.17 (G. E. Wall's conjecture, posed by R. Griess): a finite group `G` has at most
`|G| - 1` maximal subgroups. -/
def maximalSubgroupCountLtOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card {H : Subgroup G // IsCoatom H} ≤ Nat.card G - 1

/--
Resolved false: the Kourovka Archive answers 7.17 "No, not always": Guralnick, Lübeck, Scott and
Sprowl found finite groups with at least `|G|` maximal subgroups (computations at the 2012 AIM
workshop, reported by Bendel et al. 2014), and Lübeck (2020) found infinitely many. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.17 (R. Griess); resolution:
R. Guralnick, F. Lübeck, L. Scott and T. Sprowl, counterexamples found at the June 2012 AIM
workshop, see C. P. Bendel, B. D. Boe, C. M. Drupieski, D. K. Nakano, B. J. Parshall, C. Pillen and
C. B. Wright, in: Developments and retrospectives in Lie theory, Springer, 2014, 51-69; F. Lübeck,
Trans. Amer. Math. Soc. 373 (2020), 2331-2347 (infinitely many counterexamples), Kourovka Archive,
Problem 7.17: No, not always; AIM news release of 20 September 2012 (counterexample to Wall's
conjecture found at the AIM workshop), https://aimath.org/news/wallsconjecture/.
-/
public theorem_wanted maximalSubgroupCountLtOrder_refuted : ¬ maximalSubgroupCountLtOrder

end MathlibExt.GroupTheory.MaximalSubgroupCountWallKourovka7Problem17Wanted
