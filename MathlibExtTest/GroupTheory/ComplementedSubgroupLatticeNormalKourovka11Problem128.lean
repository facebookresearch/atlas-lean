/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ComplementedSubgroupLatticeNormalKourovka11Problem128

open MathlibExt.GroupTheory.ComplementedSubgroupLatticeNormalKourovka11Problem128Wanted

-- Extract an ambient group, a normal subgroup, and a subgroup with no lattice complement.
example : ∃ (G : Type) (_ : Group G), ComplementedLattice (Subgroup G) ∧
    ∃ N : Subgroup G, N.Normal ∧ ∃ A : Subgroup N, ∀ B : Subgroup N, ¬ IsCompl A B := by
  by_contra! h
  apply normalSubgroupOfKGroupIsKGroup_refuted
  intro G inst hG N hN
  exact ⟨h G inst hG N hN⟩
