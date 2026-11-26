/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Fitting height

This module defines the predicate that a group has Fitting height at most a specified bound.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Groups of Fitting height at most $h$.** For a natural number $h$, a group $G$ has Fitting
height (nilpotent length) at most $h$ if there are normal subgroups
$1 = G_0 \le G_1 \le \cdots \le G_h = G$ of $G$ such that for every $i < h$ some term of the lower
central series of $G_{i+1}$ lies in $G_i$, that is, $G_{i+1} / G_i$ is nilpotent. -/
def FittingHeightLE (G : Type*) [Group G] (h : ℕ) : Prop :=
  ∃ s : ℕ → Subgroup G, s 0 = ⊥ ∧ s h = ⊤ ∧ ∀ i < h, (s i).Normal ∧ s i ≤ s (i + 1) ∧
    ∃ c : ℕ, (s (i + 1)).lowerCentralSeries c ≤ s i

end MathlibExt.GroupTheory.KourovkaNotebookShared
