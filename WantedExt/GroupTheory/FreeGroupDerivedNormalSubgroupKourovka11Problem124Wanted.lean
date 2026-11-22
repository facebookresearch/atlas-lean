/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subgroups of free groups with normal derived subgroup (Kourovka Notebook Problem 11.124)

Kourovka Notebook, Problem 11.124 (V. E. Shpilrain): let `F` be a non-cyclic free group and `R` a
non-cyclic subgroup of `F`. If `[R, R]` is normal in `F`, is `R` normal in `F`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupDerivedNormalSubgroupKourovka11Problem124Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.124 (V. E. Shpilrain). UnsolvedMath
record UM-00700816 (`KOU-11.124`), dataset ulamai/UnsolvedMath v1.8.0.

The free group `F` is `FreeGroup α` on an arbitrary basis `α : Type` (any rank, as in the resolving
paper); non-cyclic is `¬ IsCyclic`. `[R, R]` is the commutator subgroup `⁅R, R⁆`, taken in `F`.
-/

/-- Kourovka 11.124 (V. E. Shpilrain): in a non-cyclic free group `F` (of any rank), every
non-cyclic subgroup `R` whose derived subgroup `[R, R]` is normal in `F` is itself normal in `F`. -/
def derivedNormalImpliesNormal : Prop :=
  ∀ (α : Type), ¬ IsCyclic (FreeGroup α) → ∀ R : Subgroup (FreeGroup α), ¬ IsCyclic R →
    (⁅R, R⁆).Normal → R.Normal

/--
Resolved true: Tursunbaev proves that subgroups `H`, `K` of a free group of arbitrary rank with `H'
= K' ≠ 1` coincide; for non-cyclic `R` with `R'` normal in `F`, every conjugate `R^f` has `(R^f)' =
(R')^f = R' ≠ 1`, so `R^f = R`. The Kourovka Notebook (21st issue) marks 11.124 solved, "Yes, it is
true". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.124 (V. E. Shpilrain);
resolution: A. Tursunbaev, Subgroups of free groups with the same derived subgroup, arXiv:2609.06755
(2026), main theorem (subgroups `H`, `K` of a free group of arbitrary rank with `H' = K' ≠ 1` are
equal) and its corollary answering 11.124; the Kourovka Notebook (21st issue) marks 11.124 solved,
https://arxiv.org/abs/2609.06755.
-/
public theorem_wanted derivedNormalImpliesNormal_holds : derivedNormalImpliesNormal

end MathlibExt.GroupTheory.FreeGroupDerivedNormalSubgroupKourovka11Problem124Wanted
