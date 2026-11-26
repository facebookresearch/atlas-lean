/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BranchGroupMaximalSubgroupsNormalKourovka20Problem101

open MathlibExt.GroupTheory.BranchGroupShared
open MathlibExt.GroupTheory.BranchGroupMaximalSubgroupsNormalKourovka20Problem101Wanted

-- Recover a single group and subgroup witnessing all parts of the counterexample.
example : ∃ (G : Type) (_ : Group G), Group.FG G ∧ IsBranchGroup G ∧
    ∃ M : Subgroup G, IsCoatom M ∧ M.FiniteIndex ∧ ¬ M.Normal := by
  by_contra h
  apply branchGroupFiniteIndexMaximalSubgroupsNormal_refuted
  intro G _ hfg hbranch M hmax hfin
  by_contra hn
  exact h ⟨G, inferInstance, hfg, hbranch, M, hmax, hfin, hn⟩
