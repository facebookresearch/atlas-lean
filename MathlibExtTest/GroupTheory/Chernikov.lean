/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.Chernikov

open MathlibExt.GroupTheory.GroupClassesShared

-- A finite group can use its trivial subgroup as the abelian finite-index witness.
example (G : Type*) [Group G] [Finite G] : IsChernikov G := by
  refine ⟨⊥, inferInstance, ?_, inferInstance⟩
  intro x hx y hy
  simp_all

-- A group with the minimal condition can use the whole group when it is abelian.
example (A : Type*) [CommGroup A] [h : WellFoundedLT (Subgroup A)] : IsChernikov A := by
  refine ⟨⊤, inferInstance, fun x _ y _ ↦ mul_comm x y, ?_⟩
  let e := (Subgroup.topEquiv (G := A)).mapSubgroup
  exact Subrelation.wf (fun hlt ↦ e.strictMono hlt) (InvImage.wf e h)
