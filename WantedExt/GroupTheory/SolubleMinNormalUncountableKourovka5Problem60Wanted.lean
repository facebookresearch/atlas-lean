/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uncountable soluble groups with Min-n (Kourovka Notebook Problem 5.60)

Kourovka Notebook, Archive of Solved Problems, Problem 5.60 (B. Hartley): is an arbitrary soluble
group that satisfies the minimum condition for normal subgroups countable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Countable.Defs
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleMinNormalUncountableKourovka5Problem60Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.60 (B.
Hartley). UnsolvedMath record UM-00700339 (`KOU-5.60`), dataset ulamai/UnsolvedMath v1.8.0.

Soluble is Mathlib's `Group.IsSolvable`. The minimum condition for normal subgroups (Min-n) is the
absence of a strictly descending sequence `N 0 > N 1 > ⋯` of normal subgroups.
-/

/-- Kourovka 5.60 (B. Hartley): every soluble group satisfying the minimal condition for normal
subgroups (no strictly descending infinite chain of normal subgroups) is countable. -/
def solubleMinNormalCountable : Prop :=
  ∀ (G : Type) [Group G], Group.IsSolvable G →
    (∀ N : ℕ → Subgroup G, (∀ n, (N n).Normal) → ¬ StrictAnti N) → Countable G

/--
Resolved false: the Kourovka Archive answers 5.60 "Not always", citing Hartley (1977), who
constructs uncountable soluble groups satisfying the minimal condition for normal subgroups. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.60 (B. Hartley);
resolution: B. Hartley, Uncountable Artinian modules and uncountable soluble groups satisfying
Min-n, Proc. London Math. Soc. (3) 35 (1977), 55-75 (the Archive prints volume 33), Kourovka
Archive, Problem 5.60: Not always (Hartley), https://doi.org/10.1112/plms/s3-35.1.55.
-/
public theorem_wanted solubleMinNormalCountable_refuted : ¬ solubleMinNormalCountable

end MathlibExt.GroupTheory.SolubleMinNormalUncountableKourovka5Problem60Wanted
