/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCacheData

/-! Bounded equality checks retain the original complete C and inverse-C spin models. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check both original source addresses and full quadratic phases on 256 spin inputs.
/-- Every cached C address and preferred phase in this interval is the original signed model. -/
theorem generatedSixth_xi_word_cache00 : ∀ k : Fin 2, ∀ a : Fin 256,
    let n : Fin 4096 := ⟨0 * 256 + a.val, by omega⟩
    generatedSixthXiWordCachedLabel k n =
      generatedSixthMonomialMaskLabel (generatedSixthXiWordCoordinateRows k) n.val ∧
    generatedSixthXiWordCachedPhase k n =
      (if (generatedSixthMonomialMaskQuadratic
        (fun i => (generatedSixthXiWordPhaseRows k i).val) n.val).testBit 0 then 1 else 0) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
