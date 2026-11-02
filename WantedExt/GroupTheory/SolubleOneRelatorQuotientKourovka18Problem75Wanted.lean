/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite soluble groups as images of one-relator groups (Kourovka Notebook Problem 18.75)

Kourovka Notebook, Archive of Solved Problems, Problem 18.75 (A. Yu. Olshanskii): does every finite
solvable group `G` have the following property: there is a number `d = d(G)` such that `G` is a
homomorphic image of every group with `d` generators and one relation?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleOneRelatorQuotientKourovka18Problem75Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.75 (A. Yu.
Olshanskii). UnsolvedMath record UM-00701504 (`KOU-18.75`), dataset ulamai/UnsolvedMath v1.8.0.

A group with `d` generators and one relation is `PresentedGroup {w}` for `w ∈ FreeGroup (Fin d)`.
-/

/-- **Finite soluble groups as images of one-relator groups (Kourovka 18.75).** The statement,
posed by A. Yu. Olshanskii, that every finite soluble group $G$ has a natural number $d$ such that
for every element $w$ of the free group on $x_1, \dots, x_d$ there is a surjective homomorphism
from the one-relator group $\langle x_1, \dots, x_d \mid w \rangle$ onto $G$. -/
def solubleGroupImageOfOneRelatorGroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G →
    ∃ d : ℕ, ∀ w : FreeGroup (Fin d),
      ∃ f : PresentedGroup ({w} : Set (FreeGroup (Fin d))) →* G, Function.Surjective f

/--
**Finite soluble groups are images of one-relator groups.** Every
finite soluble group $G$ has a natural number $d$ such that for every element $w$ of the free
group on $x_1, \dots, x_d$ there is a surjective homomorphism from the one-relator group
$\langle x_1, \dots, x_d \mid w \rangle$ onto $G$. That is, Kourovka Problem 18.75 has a positive
answer.

Resolved true: the Kourovka Archive answers 18.75 "Yes, it does" (N. Nikolov and D. Segal, 2007).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.75 (A. Yu.
Olshanskii); resolution: N. Nikolov and D. Segal, Bull. London Math. Soc. 39 (2007), no. 2, 209-213,
Kourovka Archive, Problem 18.75: Yes, it does, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted solubleGroupImageOfOneRelatorGroups_holds :
    solubleGroupImageOfOneRelatorGroups

end MathlibExt.GroupTheory.SolubleOneRelatorQuotientKourovka18Problem75Wanted
