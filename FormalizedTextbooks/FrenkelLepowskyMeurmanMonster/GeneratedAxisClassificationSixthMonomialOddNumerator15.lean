/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupportData

/-! Exact original odd-short integer numerators retain the complete preferred phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check all 24 physical coordinates for 64 actual original odd-code families.
/-- Every original signed numerator in this bounded odd-family interval transports exactly. -/
theorem generatedSixth_monomial_odd_numerator15 : ∀ d : Fin 64, ∀ i : Fin 24,
    let f : Fin 512 := Fin.ofNat 512 (5 * 64 + d.val)
    nortonUIntegerSign (generatedSixthMonomialOddPhase 1 f i) *
      generatedSixthFinalOddNumerator
        (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily 1 f))
        (generatedSixthMonomialPairInput 1 i) =
      generatedSixthFinalOddNumerator (generatedSixthMonomialOddCode f) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
