/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BranchGroupInfiniteIndexMaximalKourovka15Problem15

/-! # Tests for the branch group counterexample to Kourovka Problem 15.15 -/

namespace MathlibExtTest.BranchGroupInfiniteIndexMaximalKourovka15Problem15

open MathlibExt.GroupTheory.BranchGroupInfiniteIndexMaximalKourovka15Problem15Wanted

-- Recover the group and the infinite-index maximal subgroup from the refutation.
example : ∃ (G : Type) (hG : Group G), @Group.FG G hG ∧ @IsBranchGroup G hG ∧
    ∃ M : @Subgroup G hG, IsCoatom M ∧ ¬ M.FiniteIndex := by
  by_contra! h
  apply branchGroupMaximalSubgroupsFiniteIndex_refuted
  intro G hG hfg hbranch M hM
  exact h G hG hfg hbranch M hM

-- The root's subtree contains every vertex, so the rigid stabilizer at level zero is the group.
example {m : ℕ → ℕ} {G : Type*} [Group G] (ρ : G →* Equiv.Perm (TreeVertex m)) :
    rigidLevelStabilizer ρ 0 = ⊤ := by
  apply top_unique
  intro g _
  apply Subgroup.subset_closure
  refine Set.mem_iUnion₂.mpr ⟨⟨[], by simp⟩, rfl, ?_⟩
  intro w hw
  exact (hw List.nil_prefix).elim

end MathlibExtTest.BranchGroupInfiniteIndexMaximalKourovka15Problem15
