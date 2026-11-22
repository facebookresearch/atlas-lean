/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimax groups and their finite images (Kourovka Notebook Problem 12.90)

Kourovka Notebook, Archive of Solved Problems, Problem 12.90 (J. S. Wilson): let `G` be a finitely
generated soluble minimax group and `H` a finitely generated residually finite group with precisely
the same finite images as `G`. Must `H` be a minimax group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.90 (J. S.
Wilson). UnsolvedMath record UM-00700907 (`KOU-12.90`), dataset ulamai/UnsolvedMath v1.8.0.

Minimax means a finite subnormal series whose factors satisfy the maximal or the minimal condition
on subgroups. The same finite images means that the same finite groups are homomorphic images of `G`
and of `H`. Residually finite means that every nontrivial element survives in a finite quotient.
-/

/-- `G` satisfies the maximal condition on subgroups: every subgroup is finitely generated. -/
def HasMaxCondition (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG

/-- `G` satisfies the minimal condition on subgroups. -/
def HasMinCondition (G : Type*) [Group G] : Prop :=
  WellFoundedLT (Subgroup G)

/-- `G` is a minimax group: it has a finite subnormal series each of whose factors satisfies the
maximal or the minimal condition on subgroups. -/
def IsMinimax (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        HasMaxCondition (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ∨
          HasMinCondition (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- `G` and `H` have the same finite images: a finite group is a homomorphic image of `G` exactly
when it is a homomorphic image of `H`. -/
def SameFiniteImages (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (∃ f : G →* Q, Function.Surjective f) ↔ (∃ f : H →* Q, Function.Surjective f)

/-- `G` is residually finite: every nontrivial element survives in some finite quotient. -/
def IsResiduallyFinite (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ g ∉ N

/-- Kourovka 12.90 (J. S. Wilson): if `G` is a finitely generated soluble minimax group and `H`
is a finitely generated residually finite group with precisely the same finite images as `G`,
then `H` is a minimax group. -/
def minimaxDeterminedByFiniteImages : Prop :=
  ∀ (G H : Type) [Group G] [Group H], Group.FG G → Group.IsSolvable G → IsMinimax G →
    Group.FG H → IsResiduallyFinite H → SameFiniteImages G H → IsMinimax H

/--
Resolved true: the Kourovka Archive answers 12.90 "Yes, it must" (A. Mann and D. Segal, 1990; see
also A. V. Tushev, 1994). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 12.90 (J. S. Wilson); resolution: A. Mann and D. Segal, Proc. London Math. Soc. (3) 61
(1990), 529-545; A. V. Tushev, Math. Notes 56 (1994), no. 5, 1190-1192, Kourovka Archive, Problem
12.90: Yes, it must.
-/
public theorem_wanted minimaxDeterminedByFiniteImages_holds : minimaxDeterminedByFiniteImages

end MathlibExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted
