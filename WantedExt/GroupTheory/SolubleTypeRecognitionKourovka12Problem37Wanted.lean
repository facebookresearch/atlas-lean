/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solubility is not determined by the type (Kourovka Notebook Problem 12.37)

Kourovka Notebook, Problem 12.37 (J. G. Thompson; A. S. Kondratiev, W. J. Shi), marked solved in the
21st issue: for a finite group `G` let the type of `G` be the function `n ↦ |{x ∈ G | xⁿ = 1}|`. Is
a finite group soluble if its type is the same as that of a soluble group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.37 (J. G. Thompson; A. S. Kondratiev, W.
J. Shi). UnsolvedMath record UM-00700856 (`KOU-12.37`), dataset ulamai/UnsolvedMath v1.8.0.

The types are compared at every `n ≥ 1` (at `n = 0` both values are the group orders, which already
agree at `n = |G| |H|`). Groups are finite and in `Type`.
-/

/-- Two groups have the same type: for every `n ≥ 1` the equation `xⁿ = 1` has the same number of
solutions in both. -/
def SameType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, 0 < n → Nat.card {x : G // x ^ n = 1} = Nat.card {x : H // x ^ n = 1}

/-- Kourovka 12.37 (J. G. Thompson): a finite group whose type equals the type of a finite
soluble group is soluble. -/
def solubleOfSameTypeAsSoluble : Prop :=
  ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H],
    Group.IsSolvable H → SameType G H → Group.IsSolvable G

/--
Resolved false: the Kourovka Notebook (21st issue) marks 12.37 solved, "No, not always", citing P.
Piwek (Algebra Number Theory 19 (2025)): some non-soluble finite group has the same type as a
soluble finite group. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.37 (J. G. Thompson;
A. S. Kondratiev, W. J. Shi); resolution: P. Piwek, Algebra Number Theory 19 (2025), no. 8,
1663-1670, the Kourovka Notebook (21st issue) marks 12.37 solved: No, not always.
-/
public theorem_wanted solubleOfSameTypeAsSoluble_refuted : ¬ solubleOfSameTypeAsSoluble

end MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37Wanted
