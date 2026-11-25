/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FittingSubgroup

open MathlibExt.GroupTheory.NilpotentThreeConjugatesFittingKourovka17Problem40Wanted

-- For a nilpotent ambient group the join includes the whole group.
example (G : Type*) [Group G] [Group.IsNilpotent G] : fittingSubgroup G = ⊤ := by
  apply top_unique
  exact le_iSup_of_le (⊤ : Subgroup G) (le_iSup_of_le inferInstance
    (le_iSup_of_le (Group.isNilpotent_top.mpr inferInstance) le_rfl))
