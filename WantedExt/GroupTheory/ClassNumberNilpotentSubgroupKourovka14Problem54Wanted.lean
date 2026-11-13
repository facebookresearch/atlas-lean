/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Class number versus orders of nilpotent subgroups (Kourovka Notebook Problem 14.54)

Kourovka Notebook, Problem 14.54 (M. W. Liebeck, L. Pyber): let `k(G)` be the number of conjugacy
classes of a finite group `G`. Is `k(G) ≤ |N|` for some nilpotent subgroup `N` of `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.ClassNumberNilpotentSubgroupKourovka14Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.54 (M. W. Liebeck, L. Pyber).
UnsolvedMath record UM-00701039 (`KOU-14.54`), dataset ulamai/UnsolvedMath v1.8.0.

`k(G)` is `Nat.card (ConjClasses G)`; nilpotent subgroups are `Group.IsNilpotent N`.
-/

/-- **Liebeck–Pyber problem on the class number and nilpotent subgroups.** The proposition that
every finite group $G$ has a nilpotent subgroup $N$ whose order $|N|$ is at least the number
$k(G)$ of conjugacy classes of $G$. This is Kourovka Problem 14.54 (M. W. Liebeck, L. Pyber). -/
def classNumberAtMostNilpotentSubgroupOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ N : Subgroup G, Group.IsNilpotent N ∧
    Nat.card (ConjClasses G) ≤ Nat.card N

/-- **The class number can exceed the order of every nilpotent subgroup.** There is a finite group
$G$ such that the number $k(G)$ of conjugacy classes of $G$ is greater than $|N|$ for every
nilpotent subgroup $N$ of $G$.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 14.54 (M. W. Liebeck, L. Pyber); resolution: S. Tertooy, Class numbers and nilpotent
subgroups of PGL(2,q), preprint, arXiv:2606.21404 (2026), abstract: for certain odd prime powers q,
k(PGL(2,q)) exceeds the order of every nilpotent subgroup; the Kourovka Notebook (21st issue) marks
14.54 solved (No, not always), https://arxiv.org/abs/2606.21404.
-/
public theorem_wanted classNumberAtMostNilpotentSubgroupOrder_refuted :
    ¬ classNumberAtMostNilpotentSubgroupOrder

end MathlibExt.GroupTheory.ClassNumberNilpotentSubgroupKourovka14Problem54Wanted
