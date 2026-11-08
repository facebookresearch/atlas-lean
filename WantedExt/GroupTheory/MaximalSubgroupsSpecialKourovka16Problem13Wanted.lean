/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite `p`-groups whose maximal subgroups are special (Kourovka Notebook Problem 16.13)

Kourovka Notebook, Archive of Solved Problems, Problem 16.13 (Ya. G. Berkovich): does there exist a
finite `p`-group `G` all of whose maximal subgroups `H` are special, that is, satisfy `Z(H) = [H, H]
= Φ(H)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalSubgroupsSpecialKourovka16Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.13 (Ya. G.
Berkovich). UnsolvedMath record UM-00701205 (`KOU-16.13`), dataset ulamai/UnsolvedMath v1.8.0.

The literal existence question is trivially true: in the group of order `p` the only maximal
subgroup is trivial and satisfies `Z = [H, H] = Φ = 1`. The target is the Archive's answer, "for all
primes there are groups of arbitrarily large size with this property": for every prime `p` and every
`n` there is such a `G` with `|G| > n`. When `|G| > p²` every maximal subgroup has order at least
`p²`, and the condition forces it to be non-abelian. Maximal subgroups are the coatoms of the
subgroup lattice.
-/

/-- `H` is special in the sense of the problem: `Z(H) = [H, H] = Φ(H)`. -/
def IsSpecialGroup (H : Type*) [Group H] : Prop :=
  Subgroup.center H = commutator H ∧ commutator H = frattini H

/-- Kourovka 16.13 (Ya. G. Berkovich), in the form the resolution proves: for every prime `p` there
are arbitrarily large finite `p`-groups `G` all of whose maximal subgroups are special. -/
def largePGroupsWithSpecialMaximalSubgroups : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G),
    IsPGroup p G ∧ n < Nat.card G ∧ ∀ H : Subgroup G, IsCoatom H → IsSpecialGroup H

/--
Resolved true: the Kourovka Archive answers 16.13 "Yes, for all primes there are groups of
arbitrarily large size with this property", citing Cossey (2014); for `p = 2` a Sylow 2-subgroup of
`L₃(4)` is another example (Zenkov). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 16.13 (Ya. G. Berkovich); resolution: J. Cossey, Bull. Austral. Math. Soc.
89 (2014), 415-419, Kourovka Archive, Problem 16.13 (for all primes, groups of arbitrarily large
size; for p = 2 also a Sylow 2-subgroup of L_3(4), V. I. Zenkov, 2014).
-/
public theorem_wanted largePGroupsWithSpecialMaximalSubgroups_holds :
    largePGroupsWithSpecialMaximalSubgroups

end MathlibExt.GroupTheory.MaximalSubgroupsSpecialKourovka16Problem13Wanted
