/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFree
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

open MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFreeKourovka17Problem24Wanted

-- Recover an actual uncountably indexed integral basis from the existential statement.
example : ∃ (H : AddSubgroup (ℕ → ℤ)) (ι : Type), Uncountable ι ∧
    Nonempty (Module.Basis ι ℤ (H →+ ℤ)) := by
  obtain ⟨H, hfree, hrank⟩ := baerSpeckerSubgroupDualFreeUncountable_holds
  let b := Module.Free.chooseBasis ℤ (H →+ ℤ)
  refine ⟨H, _, Cardinal.aleph0_lt_mk_iff.mp ?_, ⟨b⟩⟩
  rwa [b.mk_eq_rank'']
