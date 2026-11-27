/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
-- With this import, `⨆` and `sSup` on subgroups elaborate through `CompletePartialOrder.toSupSet`
-- rather than the definitionally equal `ConditionallyCompleteLattice.toSupSet`, as in the
-- Kourovka 17.40 and 20.122 wanted modules, which import it too. This keeps the bodies of
-- `fittingSubgroup` and `inclusionMinimalIntersectionJoin` (whose module imports this one) the
-- terms those statements were written with.
public import Mathlib.Order.CompletePartialOrder

/-!
# The Fitting subgroup

`fittingSubgroup` is the join of the nilpotent normal subgroups of a group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentThreeConjugatesFittingKourovka17Problem40Wanted

/-- The Fitting subgroup `F(G)`: the join of the nilpotent normal subgroups of `G` (for finite `G`
the largest nilpotent normal subgroup). -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : Group.IsNilpotent N), N

end MathlibExt.GroupTheory.NilpotentThreeConjugatesFittingKourovka17Problem40Wanted
