/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsXiInteger
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSpinMasks

/-! Four-input integer coefficients for the genuine original source sign action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An original low dictionary row, as an executable physical spin label. -/
def generatedAxisGlobalTensorLowLabel (d : Fin 2048) : Fin 4096 := ⟨d.val, by omega⟩

/-- Its all-one translate, retaining the original physical dictionary labeling. -/
def generatedAxisGlobalTensorHighLabel (d : Fin 2048) : Fin 4096 := ⟨d.val + 2048, by omega⟩

/-- The integral physical coordinate sign of an original Golay dictionary code. -/
def generatedAxisGlobalCodeSign (d : Fin 2048) (i : Fin 24) : ℤ :=
  if (golayEncodedMask d.val).testBit i.val then -1 else 1

/-- The finite integral code sign is precisely the original physical real coordinate sign. -/
theorem generatedAxisGlobalCodeSign_real (d : Fin 2048) (i : Fin 24) :
    (generatedAxisGlobalCodeSign d i : ℝ) =
      if (golayEncodedMask d.val).testBit i.val then -1 else 1 := by
  simp [generatedAxisGlobalCodeSign]

/-- The actual low physical dictionary row has exactly its executable label. -/
theorem generatedAxisGlobalTensorLowLabel_encode (d : Fin 2048) :
    generatedAxisGlobalSpinLabel (generatedFifthSpinLow d) = generatedAxisGlobalTensorLowLabel d :=
  generatedAxisGlobalSpinLabel_coeff _

/-- The all-one translated actual physical row has exactly its executable high label. -/
theorem generatedAxisGlobalTensorHighLabel_encode (d : Fin 2048) :
    generatedAxisGlobalSpinLabel
      (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) =
        generatedAxisGlobalTensorHighLabel d := by
  change generatedAxisGlobalSpinLabel
    (golayLabelCoefficients (generatedAxisGlobalTensorLowLabel d) + Pi.single 11 1) = _
  unfold generatedAxisGlobalTensorLowLabel
  rw [golayLabel_low_add_omega, generatedAxisGlobalSpinLabel_coeff]
  rfl

/-- Complete exact integer numerator of an original source sign output coefficient. -/
def generatedAxisGlobalSignIntegerAction (N : Fin 4096 → Fin 24 → ℤ)
    (a : Fin 4096) (ε : ZMod 2) (k : Fin 4096) (i : Fin 24) : ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
    generatedAxisGlobalCodeSign e i *
    generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a ε d e) *
    generatedAxisGlobalCodeSign d i *
      (N (generatedAxisGlobalTensorLowLabel d) i - N (generatedAxisGlobalTensorHighLabel d) i) +
  generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e i) *
    (N (generatedAxisGlobalTensorLowLabel e) i + N (generatedAxisGlobalTensorHighLabel e) i)

/-- The four-input integer formula is the genuine full real tensor operator coefficient. -/
theorem generatedAxisGlobalSignIntegerAction_coefficient
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) (a : Fin 4096) (ε : ZMod 2)
    (k : Fin 4096) (i : Fin 24) :
    2 * localTensorRepresentation (generatedFifthSignFiber a ε)
        (generatedAxisGlobalTensorIntegerPacket N D) (golayLabelCoefficients k) i =
      (generatedAxisGlobalSignIntegerAction N a ε k i : ℝ) / ((D : ℝ) * Real.sqrt 2) := by
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  have hh := generatedAxisGlobalSign_tensor_coordinate a ε d e
    (golayLabelCoefficients k 11) (golayLabelCoefficients a 11)
    (generatedAxisGlobalSignInputCode_translation a e)
    (generatedAxisGlobalTensorIntegerPacket N D) i
  rw [← generatedAxisGlobalSpinLabel_split k] at hh
  rw [hh]
  simp only [generatedAxisGlobalSignIntegerAction, generatedAxisGlobalTensorIntegerPacket,
    Int.cast_add, Int.cast_sub, Int.cast_mul, generatedAxisGlobalIntSign_real,
    generatedAxisGlobalCodeSign_real, generatedAxisGlobalTensorLowLabel_encode,
    generatedAxisGlobalTensorHighLabel_encode]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
