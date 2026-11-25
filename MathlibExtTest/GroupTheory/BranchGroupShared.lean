/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BranchGroupShared

open MathlibExt.GroupTheory.BranchGroupShared

-- Every vertex descends from the unique root, so the rigid stabilizer there is the whole group.
example {T : RootedTree} {G : Type} [Group G] (A : LevelTransitiveFaithfulAction T G) :
    A.rigidLevelStabilizer 0 = ⊤ := by
  let r := T.rootUnique.default
  have desc (m : ℕ) (w : T.Vertex m) : T.IsDescendant r w := by
    induction m with
    | zero => exact (T.rootUnique.uniq w).symm ▸ RootedTree.IsDescendant.refl r
    | succ m ih => exact .child w (ih (T.parent m w))
  exact top_unique fun g _ => Subgroup.subset_closure ⟨r, fun w h => (h (desc _ w)).elim⟩
