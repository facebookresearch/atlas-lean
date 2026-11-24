/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27

namespace MathlibExtTest.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27

open MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted

/-- The theorem supplies a prime and a finite group with the stated order and subgroup bounds. -/
private theorem exactStatement :
    ∃ p : ℕ, p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G),
      IsPGroup p G ∧ 2 < Nat.card G ∧
        ∃ H : Subgroup G, H ≠ ⊤ ∧ Nonempty (MulAut G ≃* MulAut H) :=
  autIsoAutOfProperSubgroup_holds

end MathlibExtTest.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27
