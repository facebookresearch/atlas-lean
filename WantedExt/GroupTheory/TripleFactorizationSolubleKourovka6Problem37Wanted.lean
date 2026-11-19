/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups with a triple soluble factorization (Kourovka Notebook Problem 6.37)

Kourovka Notebook, Archive of Solved Problems, Problem 6.37 (V. S. Monakhov; question of H. Wielandt
and O. H. Kegel): is a finite group G soluble if it has soluble subgroups A, B, C such that G = AB =
AC = BC?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.TripleFactorizationSolubleKourovka6Problem37Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.37 (V. S.
Monakhov; question of H. Wielandt and O. H. Kegel). UnsolvedMath record UM-00700382 (`KOU-6.37`),
dataset ulamai/UnsolvedMath v1.8.0.

Products are set products of subgroups; soluble is Mathlib's `Group.IsSolvable`.
-/

open scoped Pointwise

/-- Kourovka 6.37 (H. Wielandt, O. H. Kegel; V. S. Monakhov): a finite group `G = A B = A C = B C`
with soluble subgroups `A`, `B`, `C` is soluble. -/
def tripleFactorizationSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B C : Subgroup G),
    Group.IsSolvable A → Group.IsSolvable B → Group.IsSolvable C →
    (A : Set G) * (B : Set G) = Set.univ → (A : Set G) * (C : Set G) = Set.univ →
    (B : Set G) * (C : Set G) = Set.univ → Group.IsSolvable G

/--
Resolved true: the Kourovka Archive answers 6.37 "Yes, it is (mod CFSG)", citing Kazarin (1991): a
finite group `G = A B = A C = B C` with soluble subgroups `A`, `B`, `C` is soluble. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.37 (V. S. Monakhov; question
of H. Wielandt and O. H. Kegel); resolution: L. S. Kazarin, Factorizations of finite groups by
solvable subgroups, Ukrain. Math. J. 43 (1991), 883-886, Kourovka Archive, Problem 6.37: Yes, it is
(mod CFSG) (Kazarin), https://doi.org/10.1007/BF01058687.
-/
public theorem_wanted tripleFactorizationSoluble_holds : tripleFactorizationSoluble

end MathlibExt.GroupTheory.TripleFactorizationSolubleKourovka6Problem37Wanted
