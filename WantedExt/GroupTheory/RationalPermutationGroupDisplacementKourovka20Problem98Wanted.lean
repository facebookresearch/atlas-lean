/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutation groups of the integers isomorphic to the rationals (Kourovka Notebook Problem 20.98)

Kourovka Notebook, Problem 20.98 (N. M. Suchkov), marked solved in the 21st issue: let `G` be a
group of permutations of the set of positive integers `ℕ` isomorphic to the additive group of
rational numbers. Must there be an element `g ∈ G` such that the set `{a - ag | a ∈ ℕ}` is infinite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.98 (N. M. Suchkov). UnsolvedMath record
UM-00701756 (`KOU-20.98`), dataset ulamai/UnsolvedMath v1.8.0.

Permutations act on Lean's `ℕ` (from `0`); shifting by one does not change the differences. The
Notebook's `ag` is the image of `a` under `g`, written `g a`; the differences are taken in `ℤ`. The
additive group of `ℚ` is `Multiplicative ℚ`.
-/

/-- Kourovka 20.98 (N. M. Suchkov): every group of permutations of `ℕ` isomorphic to the
additive group of the rationals contains an element `g` for which the set of displacements
`{a - g(a) : a ∈ ℕ}` (differences in `ℤ`) is infinite. -/
def rationalPermutationGroupInfiniteDisplacement : Prop :=
  ∀ G : Subgroup (Equiv.Perm ℕ), Nonempty (G ≃* Multiplicative ℚ) →
    ∃ g ∈ G, {d : ℤ | ∃ a : ℕ, (a : ℤ) - (g a : ℤ) = d}.Infinite

/--
Resolved true: the 21st issue of the Kourovka Notebook marks 20.98 solved ("Yes, it must"), citing
Suchkov, Shlepkin and Taysnyov, On the existence of countable unlimited groups, Siberian Math. J. 65
(2024), whose abstract states that `(ℚ, +)` embeds in no group of limited permutations of the
naturals: every group of permutations of `ℕ` isomorphic to `(ℚ, +)` has an element with infinitely
many displacements `a - g(a)`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.98 (N. M.
Suchkov); resolution: N. M. Suchkov, A. A. Shlepkin and D. A. Taysnyov, On the existence of
countable unlimited groups, Siberian Math. J. 65 (2024), no. 6, 1390-1394, abstract: the additive
group of the rationals is not isomorphic to a subgroup of the group of all limited permutations of
the naturals; Kourovka Notebook (21st issue), Problem 20.98: Yes, it must,
https://www.mathnet.ru/eng/smj7921.
-/
public theorem_wanted rationalPermutationGroupInfiniteDisplacement_holds :
    rationalPermutationGroupInfiniteDisplacement

end MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98Wanted
