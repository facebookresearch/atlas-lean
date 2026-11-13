/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite relatively free groups have abelian normal subgroups (Kourovka Notebook Problem 5.41)

Kourovka Notebook, Archive of Solved Problems, Problem 5.41 (A. Yu. Olshanskii): does every
non-trivial finite group which is free in some variety contain a non-trivial abelian normal
subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.HallVerbalFinitenessRelativelyFreeKourovka12Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.RelativelyFreeFiniteAbelianNormalKourovka5Problem41Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.41 (A. Yu.
Olshanskii). UnsolvedMath record UM-00700323 (`KOU-5.41`), dataset ulamai/UnsolvedMath v1.8.0.

Free in some variety (relatively free) is `IsRelativelyFree` of the Kourovka 12.31 entry, reused
here: a generating family every assignment of which extends to an endomorphism of `G`; such a group
is free in the variety it generates. Abelian normal subgroup: a normal subgroup whose elements
commute pairwise.
-/

open MathlibExt.GroupTheory.HallVerbalFinitenessRelativelyFreeKourovka12Problem31Wanted
  (IsRelativelyFree)

/-- Kourovka 5.41 (A. Yu. Olshanskii): every non-trivial finite group that is free in some variety
has a non-trivial abelian normal subgroup; free in some variety is `IsRelativelyFree` (a generating
family every assignment of which extends to an endomorphism). -/
def relativelyFreeFiniteHasAbelianNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Nontrivial G], IsRelativelyFree G →
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

/--
Resolved true: the Kourovka Archive answers 5.41 "Yes, it does (mod CFSG)" with Syskin's argument
(letter of 20 August 1992): in a counterexample `G` the product `E` of the minimal normal subgroups
has trivial centralizer and `G / E` has an element of order `m`, the largest order of a `2`-element
of `G`; Theorem 1 of Aschbacher, Kleidman and Liebeck (Math. Z. 208 (1991)), proved using CFSG, then
gives an element of order `2m` in `G`, a contradiction. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 5.41 (A. Yu. Olshanskii); resolution: S. A. Syskin,
letter of 20 August 1992, using M. Aschbacher, P. B. Kleidman and M. W. Liebeck, Exponents of almost
simple groups and an application to the restricted Burnside problem, Math. Z. 208 (1991), 401-409,
Theorem 1, Kourovka Archive, Problem 5.41: Yes, it does (mod CFSG); in a counterexample the
centralizer of the product E of the minimal normal subgroups is trivial and G/E has an element of
order m, the largest order of a 2-element of G, so by Theorem 1 of Aschbacher-Kleidman-Liebeck G has
an element of order 2m, a contradiction (Syskin), https://doi.org/10.1007/BF02571536.
-/
public theorem_wanted relativelyFreeFiniteHasAbelianNormal_holds :
    relativelyFreeFiniteHasAbelianNormal

end MathlibExt.GroupTheory.RelativelyFreeFiniteAbelianNormalKourovka5Problem41Wanted
