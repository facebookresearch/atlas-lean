/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Residual nilpotence of free central extensions (Kourovka Notebook Problem 16.65)

Kourovka Notebook, Archive of Solved Problems, Problem 16.65 (R. Mikhailov, I. B. S. Passi): does
there exist a finitely presented residually torsion-free nilpotent group with a free presentation `G
= F/R` such that the group `F/[F, R]` is not residually nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.FreeCentralExtensionResiduallyNilpotentKourovka16Problem65Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.65 (R.
Mikhailov, I. B. S. Passi). UnsolvedMath record UM-00701257 (`KOU-16.65`), dataset
ulamai/UnsolvedMath v1.8.0.

A free presentation is a free group `F = FreeGroup α` on any type `α` with a normal subgroup `R`;
`[F, R]` is the commutator subgroup `⁅⊤, R⁆`. Residually (torsion-free) nilpotent means that every
nontrivial element survives in some (torsion-free) nilpotent quotient.
-/

/-- `G` is residually nilpotent: every `g ≠ 1` survives in some nilpotent quotient. -/
def IsResiduallyNilpotent (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, ∃ _ : N.Normal, g ∉ N ∧ Group.IsNilpotent (G ⧸ N)

/-- `G` is residually torsion-free nilpotent: every `g ≠ 1` survives in some torsion-free nilpotent
quotient. -/
def IsResiduallyTorsionFreeNilpotent (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, ∃ _ : N.Normal, g ∉ N ∧ Group.IsNilpotent (G ⧸ N) ∧
    ∀ x : G ⧸ N, x ≠ 1 → ¬ IsOfFinOrder x

/-- Kourovka 16.65 (R. Mikhailov, I. B. S. Passi): there are a finitely presented residually
torsion-free nilpotent group `G` and a free presentation `G = F / R` such that `F / [F, R]` is not
residually nilpotent. -/
def existsPresentationWithNonResiduallyNilpotentQuotient : Prop :=
  ∃ (α : Type) (R : Subgroup (FreeGroup α)) (_ : R.Normal),
    Group.IsFinitelyPresented (FreeGroup α ⧸ R) ∧
    IsResiduallyTorsionFreeNilpotent (FreeGroup α ⧸ R) ∧
    ¬ IsResiduallyNilpotent (FreeGroup α ⧸ ⁅(⊤ : Subgroup (FreeGroup α)), R⁆)

/--
Resolved true: the Kourovka Archive answers 16.65 "Yes, there does", citing Bludov (2009). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.65 (R. Mikhailov, I.
B. S. Passi); resolution: V. V. Bludov, J. Group Theory 12 (2009), no. 4, 579-590, Kourovka Archive,
Problem 16.65 (Yes, there does).
-/
public theorem_wanted existsPresentationWithNonResiduallyNilpotentQuotient_holds :
    existsPresentationWithNonResiduallyNilpotentQuotient

end MathlibExt.GroupTheory.FreeCentralExtensionResiduallyNilpotentKourovka16Problem65Wanted
