/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecads

/-! The original Golay dodecads containing both coordinates of the norm-four root. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original encoder labels of dodecads containing coordinates zero and one. -/
def leechNormSixPairDodecads : Finset (Fin 4096) :=
  golayDodecads.filter fun d => (golayEncodedMask d.val).testBit 0 = true ∧
    (golayEncodedMask d.val).testBit 1 = true

set_option maxHeartbeats 8000000 in
-- Count all original encoder outputs with both physical support bits present.
set_option maxRecDepth 10000 in
/-- Exactly 616 original dodecads contain the fixed pair. -/
theorem leechNormSixPairDodecads_card : leechNormSixPairDodecads.card = 616 := by
  decide +kernel

/-- Membership states weight twelve and the two original encoded support bits. -/
theorem leechNormSixPairDodecads_mem_iff (d : Fin 4096) :
    d ∈ leechNormSixPairDodecads ↔ golayMaskWeight (golayEncodedMask d.val) = 12 ∧
      (golayEncodedMask d.val).testBit 0 = true ∧
      (golayEncodedMask d.val).testBit 1 = true := by
  simp only [leechNormSixPairDodecads, golayDodecads, Finset.mem_filter,
    Finset.mem_univ, true_and]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
