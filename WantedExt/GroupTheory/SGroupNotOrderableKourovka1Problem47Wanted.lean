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
# `S`-groups that are not orderable (Kourovka Notebook Problem 1.47)

Kourovka Notebook, Archive of Solved Problems, Problem 1.47 (A. I. Kokorin): a subgroup `H` of `G`
is strictly isolated if, whenever `x g₁⁻¹xg₁ ⋯ gₙ⁻¹xgₙ` belongs to `H`, so do `x` and each
`gᵢ⁻¹xgᵢ`. A group in which the identity subgroup is strictly isolated is an `S`-group. Do there
exist `S`-groups that are not orderable groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Defs.LinearOrder
public import MathlibExt.GroupTheory.Orderability
public import WantedExt.GroupTheory.StrictlyIsolatedAbelianInvariantOrderKourovka1Problem49Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SGroupNotOrderableKourovka1Problem47Wanted

open MathlibExt.GroupTheory.StrictlyIsolatedAbelianInvariantOrderKourovka1Problem49Wanted

export MathlibExt.GroupTheory (IsBiInvariantOrder IsOrderable)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.47 (A. I.
Kokorin). UnsolvedMath record UM-00700042 (`KOU-1.47`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). For the identity subgroup,
strict isolation says that `x g₁⁻¹xg₁ ⋯ gₙ⁻¹xgₙ = 1` implies `x = 1` (the conjugates are then `1` as
well).
-/

/-- Kourovka 1.47 (A. I. Kokorin): there is an `S`-group that is not orderable. -/
def existsNonOrderableSGroup : Prop :=
  ∃ (G : Type) (_ : Group G), IsSGroup G ∧ ¬ IsOrderable G

/--
Resolved true: the Kourovka Archive answers 1.47 "Yes, such groups do exist", citing Bludov (1974);
Bludov's earlier paper (1972) is titled An example of an unordered group with strictly isolated
identity element, that is, a non-orderable `S`-group. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 1.47 (A. I. Kokorin); resolution: V. V. Bludov, Algebra
and Logic 13 (1974), 343-360; V. V. Bludov, An example of an unordered group with strictly isolated
identity element, Algebra and Logic 11 (1972), 341-349, Kourovka Archive, Problem 1.47 (Yes, such
groups do exist).
-/
public theorem_wanted existsNonOrderableSGroup_holds : existsNonOrderableSGroup

private example : ProofWanted.Stmt existsNonOrderableSGroup_holds ↔ existsNonOrderableSGroup :=
  Iff.rfl

end MathlibExt.GroupTheory.SGroupNotOrderableKourovka1Problem47Wanted
