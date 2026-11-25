/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Maximal abelian normal subgroups of orderable groups (Kourovka Notebook Problem 1.44)

Kourovka Notebook, Archive of Solved Problems, Problem 1.44 (A. I. Kokorin): is a maximal abelian
normal subgroup relatively convex?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalAbelianNormalRelativelyConvexKourovka1Problem44Wanted

export MathlibExt.GroupTheory
  (IsBiInvariantOrder IsOrderable IsRelativelyConvex)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.44 (A. I.
Kokorin). UnsolvedMath record UM-00700039 (`KOU-1.44`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). A subgroup is relatively convex
(Kourovka Archive 1.41) if it is convex for some such order of `G`; for a subgroup, convexity is the
condition `1 ≤ g ≤ h`, `h ∈ H` implies `g ∈ H`. A maximal abelian normal subgroup is an abelian
normal subgroup contained in no strictly larger abelian normal subgroup.
-/

/-- `A` is a maximal abelian normal subgroup of `G`: an abelian normal subgroup contained in no
strictly larger abelian normal subgroup. -/
def IsMaximalAbelianNormal {G : Type} [Group G] (A : Subgroup G) : Prop :=
  A.Normal ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
    ∀ B : Subgroup G, B.Normal → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A

/-- Kourovka 1.44 (A. I. Kokorin): every maximal abelian normal subgroup of an orderable group is
relatively convex. -/
def maximalAbelianNormalIsRelativelyConvex : Prop :=
  ∀ (G : Type) [Group G] (A : Subgroup G), IsOrderable G → IsMaximalAbelianNormal A →
    IsRelativelyConvex A

/--
Resolved false: the Kourovka Archive answers 1.44 "Not always", citing Smirnov (1966): some
orderable group has a maximal abelian normal subgroup that is not relatively convex. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.44 (A. I. Kokorin);
resolution: D. M. Smirnov, Algebra i Logika 5 (1966), no. 6, 41-60 (Russian), Kourovka Archive,
Problem 1.44 (Not always).
-/
public theorem_wanted maximalAbelianNormalIsRelativelyConvex_refuted :
    ¬ maximalAbelianNormalIsRelativelyConvex

private example : ProofWanted.Stmt maximalAbelianNormalIsRelativelyConvex_refuted ↔
    ¬ maximalAbelianNormalIsRelativelyConvex :=
  Iff.rfl

end MathlibExt.GroupTheory.MaximalAbelianNormalRelativelyConvexKourovka1Problem44Wanted
