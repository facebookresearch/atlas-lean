/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorFactors

/-! Ungated rational source bridge. Every factor comes from the actual Root02 word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Rational incoming tensor before its genuine common square-root-two normalization. -/
def generatedTenthFinalShortSourceTensorQ (k : Fin 4096) (i : Fin 24) : ℚ :=
  ∑ r : Fin 8,
    let v := generatedTenthTensorFactorData r 7
    ((v.1 k : ℚ) * (v.2.1 i : ℚ)) / (v.2.2.1 * v.2.2.2 : ℕ)

/-- Every full incoming tensor coordinate retains the already proved eight-factor source. -/
theorem generatedTenth_final_short_source_tensor_actual (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 (golayLabelCoefficients k) i =
      (generatedTenthFinalShortSourceTensorQ k i : ℝ) / Real.sqrt 2 := by
  have hf (r : Fin 8) :
      generatedTenthTensorFactor r 7 (golayLabelCoefficients k) i =
        (((generatedTenthTensorFactorData r 7).1 k *
          (generatedTenthTensorFactorData r 7).2.1 i : ℤ) : ℝ) /
        ((((generatedTenthTensorFactorData r 7).2.2.1 *
          (generatedTenthTensorFactorData r 7).2.2.2 : ℕ) : ℝ) * Real.sqrt 2) := by
    exact generatedAxisGlobalTensorIntegerPacket_coefficient _ _ k i
  rw [generatedTenth_incoming_tensor_factors]
  simp only [Finset.sum_apply]
  simp_rw [hf]
  unfold generatedTenthFinalShortSourceTensorQ
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  simp only [div_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
