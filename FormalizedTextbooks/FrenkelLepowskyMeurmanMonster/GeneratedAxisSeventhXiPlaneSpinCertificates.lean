/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinData

/-! Every compact spin coefficient is bound to the original genuine fixing Pauli product. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The 4096 finite labels retain both exact support and original fixing-product central phases.
/-- The finite normalized spin masks agree with the genuine Pauli equations and coefficients. -/
theorem generatedSeventhXiPlaneSpin_cache : ∀ b i : Fin 64,
    let d : Fin 4096 := ⟨64 * b.val + i.val, by omega⟩
    let t := golayLabelCoefficients d
    (((generatedSeventhXiPlaneSpinSupportRows b).testBit i.val = true) ↔
      generatedSeventhSpinSupportMatrix *ᵥ t = 0) ∧
    (generatedSeventhSpinSupportMatrix *ᵥ t = 0 →
      spinPhase (generatedSeventhSpinPauliProduct
        (generatedSeventhSpinPauliLeftInverse *ᵥ t)) 0 =
        golayBooleanCast ((generatedSeventhXiPlaneSpinNegativeRows b).testBit i.val)) := by
  intro b
  fin_cases b <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
