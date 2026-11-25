/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Index

/-!
# Residually finite `p`-groups

`IsResiduallyFiniteP p G` says that every nontrivial element of the group `G` lies outside some
normal subgroup of `G` of `p`-power index.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Residually finite $p$-groups.** For a natural number $p$, a group $G$ is residually a finite
$p$-group if every element $g \ne 1$ of $G$ lies outside some normal subgroup of $G$ whose index
is $p^k$ for some $k \ge 0$, where an infinite index counts as $0$.

This notion appears in Kourovka Notebook problems 1.84, 4.52 and 10.30. -/
def IsResiduallyFiniteP (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, N.Normal ∧ (∃ k : ℕ, N.index = p ^ k) ∧ g ∉ N

end MathlibExt.GroupTheory.KourovkaNotebookShared
