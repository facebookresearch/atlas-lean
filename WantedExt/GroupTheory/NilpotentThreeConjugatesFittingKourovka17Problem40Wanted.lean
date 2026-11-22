/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three conjugates of a nilpotent subgroup meeting in `F(G)` (Kourovka Notebook Problem 17.40)

Kourovka Notebook, Archive of Solved Problems, Problem 17.40 (E. P. Vdovin): let `N` be a nilpotent
subgroup of a finite group `G`. Do there always exist elements `x, y ∈ G` such that `N ∩ N^x ∩ N^y ≤
F(G)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentThreeConjugatesFittingKourovka17Problem40Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.40 (E. P.
Vdovin). UnsolvedMath record UM-00701342 (`KOU-17.40`), dataset ulamai/UnsolvedMath v1.8.0.

`F(G)` is the join of the nilpotent normal subgroups of `G` (for finite `G` the largest nilpotent
normal subgroup); `N^x` is the image of `N` under conjugation by `x` (the direction is immaterial as
`x` ranges over `G`).
-/

/-- The Fitting subgroup `F(G)`: the join of the nilpotent normal subgroups of `G` (for finite `G`
the largest nilpotent normal subgroup). -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : Group.IsNilpotent N), N

/-- Kourovka 17.40 (E. P. Vdovin): for every nilpotent subgroup `N` of a finite group `G` there are
`x, y ∈ G` with `N ∩ N^x ∩ N^y ≤ F(G)`. -/
def nilpotentThreeConjugatesInFitting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), Group.IsNilpotent N →
    ∃ x y : G, N ⊓ N.map (MulAut.conj x).toMonoidHom ⊓ N.map (MulAut.conj y).toMonoidHom ≤
      fittingSubgroup G

/--
Resolved true: the Kourovka Archive answers 17.40 "Yes, such elements always exist, mod CFSG",
citing Zenkov (2021): for every nilpotent subgroup `N` of a finite group `G` there are `x, y ∈ G`
with `N ∩ N^x ∩ N^y ≤ F(G)`. The proof uses the classification of finite simple groups. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.40 (E. P. Vdovin);
resolution: V. I. Zenkov, Siberian Math. J. 62 (2021), 621-637, Kourovka Archive, Problem 17.40
(Yes, such elements always exist, mod CFSG).
-/
public theorem_wanted nilpotentThreeConjugatesInFitting_holds : nilpotentThreeConjugatesInFitting

end MathlibExt.GroupTheory.NilpotentThreeConjugatesFittingKourovka17Problem40Wanted
