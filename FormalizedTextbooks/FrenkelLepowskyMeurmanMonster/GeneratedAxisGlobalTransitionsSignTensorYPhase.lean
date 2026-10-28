/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignTensorZPhase

/-! Finite exact source polynomial phases for the complementary Y tensor dictionary. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact source Parker, modulation, and dictionary-normalization phases on a Y column. -/
def generatedAxisGlobalSignYPhase (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) : ZMod 2 :=
  ε + (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) +
    spinDot (sourceWordTheta a) (generatedFifthSpinLow e) +
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
    (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)

/-- The original source dictionary phase is exactly the finite displayed polynomial. -/
theorem generatedAxisGlobalSignYPhase_eq (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) :
    generatedFifthSignDictionaryPhase (sourceQCode a ε) d e =
      generatedAxisGlobalSignYPhase a ε d e := by
  have hc : Multiplicative.toAdd (sourceQCode a ε).coeff =
      ε + (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) := rfl
  rw [generatedFifthSignDictionaryPhase, spinPhase, hc, sourceQCode_modulation,
    ← sourceWordTheta_polynomial]
  rfl

/-- Every checked source-code translation has its exact executable actual Y tensor action. -/
theorem generatedAxisGlobalSign_tensor_Y_polynomial (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (i : Fin 24) :
    localTensorRepresentation (generatedFifthSignFiber a ε) (trialityYTensor d i) =
      qSign (generatedAxisGlobalSignYPhase a ε d e) • trialityYTensor e i := by
  rw [generatedFifth_sign_tensor_Y a ε d e h he i, generatedAxisGlobalSignYPhase_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
