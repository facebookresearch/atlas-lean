/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiLiteralTensor

/-! Full original corrected tensor fixation on the final sixty-four actual spin addresses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 64000000 in
-- Check every original nonzero tensor coordinate in this interval with all Gaussian terms.
/-- The original corrected Xi numerator is exact on all nonzero coordinates in this interval. -/
theorem generatedSixth_xi_literal_fix63 : ∀ a : Fin 64, ∀ i : Fin 24,
    let n : Fin 4096 := ⟨63 * 64 + a.val, by omega⟩
    generatedSixthTensorFastExecutable n i ≠ 0 →
      generatedSixthXiCachedTensor n i = 16 * generatedSixthTensorFastExecutable n i := by
  have h : ∀ a : Fin 64, ∀ i : Fin 24,
      let n : Fin 4096 := ⟨63 * 64 + a.val, by omega⟩
      generatedSixthTensorFastExecutable n i ≠ 0 →
        generatedSixthXiLiteralTensor n i = 16 * generatedSixthTensorFastExecutable n i := by
    decide +kernel
  intro a i
  have hh := h a i
  dsimp only at hh ⊢
  rw [generatedSixth_xi_literal_tensor] at hh
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
