/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups of the form ABA (Kourovka Notebook Problem 9.63)

Kourovka Notebook, Archive of Solved Problems, Problem 9.63 (Ya. P. Sysak): is a finite group of the
form `G = ABA` soluble if `A` is an abelian subgroup and `B` is a cyclic subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianCyclicTripleProductSolubleKourovka9Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.63 (Ya. P.
Sysak). UnsolvedMath record UM-00700596 (`KOU-9.63`), dataset ulamai/UnsolvedMath v1.8.0.

`G = ABA` means that every element is a product `aba'` with `a, a' ∈ A`, `b ∈ B` (`(A : Set G) * B *
A = univ`). The proof uses the classification of finite simple groups.
-/

open scoped Pointwise

/-- Kourovka 9.63 (Ya. P. Sysak): a finite group `G = ABA`, with `A` an abelian subgroup and `B` a
cyclic subgroup, is soluble. -/
def abaFactorizedSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    IsCyclic B → (A : Set G) * (B : Set G) * (A : Set G) = Set.univ → Group.IsSolvable G

/--
Resolved true: Zagorin and Kazarin prove that a finite group `ABA` with `A` abelian and `B` cyclic
is soluble (Theorem 2, as stated in the zbMATH review Zbl 0895.20020; the proof uses the
classification of finite simple groups); the Kourovka Archive answers 9.63 "Yes, it is soluble (mod
CFSG)". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.63
(Ya. P. Sysak); resolution: D. L. Zagorin and L. S. Kazarin, Abelian ABA-factorizations of finite
groups, Dokl. Math. 53 (1996), no. 2, 237-239, Theorem 2 as stated in the zbMATH review Zbl
0895.20020: a finite ABA-group with abelian A and cyclic B is soluble (the proof uses the
classification of finite simple groups); Kourovka Archive of Solved Problems, Problem 9.63: Yes, it
is soluble (mod CFSG), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted abaFactorizedSoluble_holds : abaFactorizedSoluble

end MathlibExt.GroupTheory.AbelianCyclicTripleProductSolubleKourovka9Problem63Wanted
