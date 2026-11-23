/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of two soluble subgroups of odd index (Kourovka Notebook Problem 8.48)

Kourovka Notebook, Archive of Solved Problems, Problem 8.48 (V. S. Monakhov): if a finite group `G`
can be written as the product of two soluble subgroups of odd index, then is `G` soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.OddIndexSolubleFactorizationKourovka8Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.48 (V. S.
Monakhov). UnsolvedMath record UM-00700498 (`KOU-8.48`), dataset ulamai/UnsolvedMath v1.8.0.

`G = AB` means every element is `ab` with `a ∈ A`, `b ∈ B`; indices are `Subgroup.index`.
-/

/-- Kourovka 8.48 (V. S. Monakhov): a finite group `G = AB` that is the product of two soluble
subgroups `A` and `B` of odd index is soluble. -/
def oddIndexSolubleFactorizationSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G), (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) →
    Group.IsSolvable A → Group.IsSolvable B → Odd A.index → Odd B.index → Group.IsSolvable G

/--
Resolved true: the Kourovka Archive answers 8.48 "Yes, it is", modulo the classification of finite
simple groups, citing Kazarin, Factorizations of finite groups by solvable subgroups (1991). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.48 (V. S. Monakhov);
resolution: L. S. Kazarin, Factorizations of finite groups by solvable subgroups, Ukrainian Math. J.
43 (1991), 883-886, Kourovka Archive, Problem 8.48: Yes, it is (mod CFSG); paper, Theorem 3 (zbMATH
Zbl 0738.20028), https://doi.org/10.1007/BF01058687.
-/
public theorem_wanted oddIndexSolubleFactorizationSoluble_holds :
    oddIndexSolubleFactorizationSoluble

end MathlibExt.GroupTheory.OddIndexSolubleFactorizationKourovka8Problem48Wanted
