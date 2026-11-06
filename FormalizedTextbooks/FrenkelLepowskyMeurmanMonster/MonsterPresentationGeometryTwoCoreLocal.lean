/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The intrinsic local normal two-core is the actual extraspecial kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalTwoSubgroupExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual local projection kernel is a two-group of its proved order 2^25. -/
theorem monsterGeometryLocalKernel_isTwoGroup : IsPGroup 2 projH.ker :=
  IsPGroup.of_card projH_kernel_card

/-- The intrinsic O₂(H) is exactly the genuine extraspecial image, without a recognition input. -/
theorem monsterGeometryLocalTwoCore_eq_Q :
    monsterGeometryTwoCore H = inclQ.range := by
  rw [inclQ_range_eq_projH_ker]
  apply monsterGeometryTwoCore_eq_kernel projH projH_surjective
    monsterGeometryLocalKernel_isTwoGroup
  intro P hnormal hP
  have : P.Normal := hnormal
  exact co1_normal_two_subgroup_eq_bot P hP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
