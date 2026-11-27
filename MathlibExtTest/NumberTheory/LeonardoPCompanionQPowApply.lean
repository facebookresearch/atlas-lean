/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPCompanionQPowApply

namespace MathlibExtTest.NumberTheory.LeonardoPCompanionQPowApply

-- Identity at distinct indices in the top row uses `A_p(0) = 0`.
example : (MathlibExt.NumberTheory.LeonardoPWanted.companionQ 2 ^ 0)
    ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
  have hth := MathlibExt.NumberTheory.LeonardoPWanted.companionQ_pow_apply 2 0
    (by decide) ⟨0, by decide⟩ ⟨1, by decide⟩
  rw [hth]
  decide

-- Identity on a `B_p` row uses `B_p(-p + 1) = 1`.
example : (MathlibExt.NumberTheory.LeonardoPWanted.companionQ 2 ^ 0)
    ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by
  have hth := MathlibExt.NumberTheory.LeonardoPWanted.companionQ_pow_apply 2 0
    (by decide) ⟨1, by decide⟩ ⟨1, by decide⟩
  rw [hth]
  decide

-- Identity on the first `B_p` row at `p = 3` uses the corrected index: the entry is
-- `B_3(-2) = 1`, where the printed index direction would give `B_3(0) = 0`.
example : (MathlibExt.NumberTheory.LeonardoPWanted.companionQ 3 ^ 0)
    ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by
  have hth := MathlibExt.NumberTheory.LeonardoPWanted.companionQ_pow_apply 3 0
    (by decide) ⟨1, by decide⟩ ⟨1, by decide⟩
  rw [hth]
  decide

-- The first power entry in the top-left corner is `A_p(2) = 1`.
example : (MathlibExt.NumberTheory.LeonardoPWanted.companionQ 2 ^ 1)
    ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
  have hth := MathlibExt.NumberTheory.LeonardoPWanted.companionQ_pow_apply 2 1
    (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩
  rw [hth]
  decide

-- Identity on the last row uses `-A_p(-2 * p) = 1`.
example : (MathlibExt.NumberTheory.LeonardoPWanted.companionQ 2 ^ 0)
    ⟨4, by decide⟩ ⟨4, by decide⟩ = 1 := by
  have hth := MathlibExt.NumberTheory.LeonardoPWanted.companionQ_pow_apply 2 0
    (by decide) ⟨4, by decide⟩ ⟨4, by decide⟩
  rw [hth]
  decide

end MathlibExtTest.NumberTheory.LeonardoPCompanionQPowApply
