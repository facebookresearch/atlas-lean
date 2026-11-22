/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally nilpotent subgroups and the Hirsch-Plotkin radical

Shared definitions for the Kourovka Notebook entries on locally nilpotent groups (Problems 1.45,
2.58 and 2.64): a subgroup is locally nilpotent when each of its finitely generated subgroups is
nilpotent (a group is locally nilpotent when `⊤` is), and the Hirsch-Plotkin radical is the join of
the locally nilpotent normal subgroups. Moved unchanged from
`HirschPlotkinRadicalRelativelyConvexKourovka1Problem45Wanted`.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyNilpotentShared

/-- The subgroup `N` is locally nilpotent: every finitely generated subgroup of `N` is nilpotent. -/
def IsLocallyNilpotent {G : Type} [Group G] (N : Subgroup G) : Prop :=
  ∀ s : Finset G, (s : Set G) ⊆ N → Group.IsNilpotent (Subgroup.closure (s : Set G))

/-- The Hirsch-Plotkin radical of `G`: the join of all locally nilpotent normal subgroups, which is
the largest locally nilpotent normal subgroup by the Hirsch-Plotkin theorem. -/
def hirschPlotkinRadical (G : Type) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ IsLocallyNilpotent N}

end MathlibExt.GroupTheory.LocallyNilpotentShared
