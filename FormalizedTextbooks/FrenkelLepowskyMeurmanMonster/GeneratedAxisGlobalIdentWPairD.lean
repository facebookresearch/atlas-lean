/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory: the pair self part of a target with distinct pair labels (gident2)

With pairwise distinct pair labels (r8f's bitmap check `labDistinct`) the collapsed pair self sum
`selfPairsZ` is the sum of the squares of the pair values, a single pass. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The collapsed pair self sum is the sum of squares when the pair labels are distinct. -/
theorem selfPairsZ_of_distinct (V : IdentVec) (h : labDistinct V.sh.pairs 0 = true) :
    selfPairsZ V = sqSumZ V.sh.pairs := by
  have hn := (labDistinct_spec _ _ h).2
  unfold selfPairsZ sqSumZ
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [idxSum_of_nodup _ hn q hq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
