/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Inclusion of derived subgroups in free groups (Kourovka Notebook Problem 13.62)

Kourovka Notebook, Archive of Solved Problems, Problem 13.62 (V. P. Shaptala): let `U` and `V` be
non-cyclic subgroups of a free group. Does `[U, U] ≤ [V, V]` imply `U ≤ V`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.DerivedSubgroupInclusionFreeGroupKourovka13Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.62 (V. P.
Shaptala). UnsolvedMath record UM-00700980 (`KOU-13.62`), dataset ulamai/UnsolvedMath v1.8.0.

Free groups of every rank (`FreeGroup α`, `α : Type`); `[U, U]` is the commutator subgroup `⁅U, U⁆`
of `U` as a subgroup of the free group.
-/

/-- Kourovka 13.62 (V. P. Shaptala): for non-cyclic subgroups `U` and `V` of a free group, the
inclusion `[U, U] ≤ [V, V]` implies `U ≤ V`. -/
def derivedInclusionImpliesInclusion : Prop :=
  ∀ (α : Type) (U V : Subgroup (FreeGroup α)), ¬ IsCyclic U → ¬ IsCyclic V →
    ⁅U, U⁆ ≤ ⁅V, V⁆ → U ≤ V

/--
Resolved false: the Kourovka Archive answers 13.62 "No, it does not", citing Dunwoody: some free
group has non-cyclic subgroups `U`, `V` with `[U, U] ≤ [V, V]` but `U` not contained in `V`. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.62 (V. P. Shaptala);
resolution: M. J. Dunwoody, Arch. Math. 16 (1965), 153-157, Kourovka Archive, Problem 13.62 (answer:
No, it does not).
-/
public theorem_wanted derivedInclusionImpliesInclusion_refuted : ¬ derivedInclusionImpliesInclusion

end MathlibExt.GroupTheory.DerivedSubgroupInclusionFreeGroupKourovka13Problem62Wanted
