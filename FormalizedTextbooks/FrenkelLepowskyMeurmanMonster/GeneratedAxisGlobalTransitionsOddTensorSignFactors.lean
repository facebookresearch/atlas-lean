/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFourierPhases

/-! Exact integral separation of the full low-code source sign tensor action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem oddSign_input_low (a e : Fin 2048) :
    generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e =
      monsterNortonEvenCodeSum a e := by
  have h := generatedAxisGlobalSignInputCode_translation (generatedAxisGlobalSignLowCode a) e
  rw [show golayLabelCoefficients (generatedAxisGlobalSignLowCode a) 11 = 0 from
    golayLabel_low_last a, zero_smul, add_zero, generatedAxisGlobalSignLow_translation] at h
  change golayLabelCoefficients ⟨(monsterNortonEvenCodeSum a e).val, by omega⟩ =
    golayLabelCoefficients
      ⟨(generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e).val,
        by omega⟩ at h
  exact Fin.ext (congrArg Fin.val (golayLabelCoefficients_bijective.injective h)).symm

private theorem oddSign_code_products (a e : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalCodeSign e i *
      generatedAxisGlobalCodeSign
        (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e) i =
      generatedAxisGlobalCodeSign a i := by
  rw [oddSign_input_low]
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, generatedAxisGlobalCodeSign_real]
  have h := generatedAxisGlobalSignLow_code_signs a e i
  change _ = qSign (golayEncoder (golayLabelCoefficients ⟨a.val, by omega⟩) i) at h
  rw [golayEncoder_low_qSign] at h
  exact h

private theorem oddSign_Z_spatial (a e : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalIntSign
        (generatedAxisGlobalSignZPhase (generatedAxisGlobalSignLowCode a) e i) =
      generatedAxisGlobalCodeSign a i * generatedAxisGlobalCodeSign a 0 *
        generatedAxisGlobalIntSign
          (generatedAxisGlobalSignZPhase (generatedAxisGlobalSignLowCode a) e 0) := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, generatedAxisGlobalIntSign_real, generatedAxisGlobalCodeSign_real]
  rw [← golayEncoder_low_qSign, ← golayEncoder_low_qSign,
    generatedAxisGlobalSignLow_ZPhase, generatedAxisGlobalSignLow_ZPhase]
  change _ = qSign (golayEncoder (monsterNortonYCode a) i) *
    qSign (golayEncoder (monsterNortonYCode a) 0) *
      (qSign (golayEncoder (monsterNortonYCode a) 0) * _)
  rw [mul_assoc, ← mul_assoc (qSign (golayEncoder (monsterNortonYCode a) 0)),
    qSign_sq, one_mul]

/-- The complete four-input spin numerator of the actual low-code source sign operation. -/
def generatedAxisGlobalOddSignSpinInteger (a : Fin 2048) (u : Fin 4096 → ℤ)
    (k : Fin 4096) : ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a) e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
    generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
      (generatedAxisGlobalSignLowCode a) 0 d e) *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) +
  generatedAxisGlobalCodeSign a 0 *
    generatedAxisGlobalIntSign
      (generatedAxisGlobalSignZPhase (generatedAxisGlobalSignLowCode a) e 0) *
      (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e))

/-- The original physical spatial code sign, with its full coordinate orientation. -/
def generatedAxisGlobalOddSignSpatialInteger (a : Fin 2048) (v : Fin 24 → ℤ)
    (i : Fin 24) : ℤ := generatedAxisGlobalCodeSign a i * v i

/-- The true four-input tensor formula separates into exact spin and spatial integer factors. -/
theorem generatedAxisGlobalOddSignInteger_factor (a : Fin 2048)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalSignIntegerAction (generatedAxisGlobalOddTensorFactor u v)
        (generatedAxisGlobalSignLowCode a) 0 =
      generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddSignSpinInteger a u)
        (generatedAxisGlobalOddSignSpatialInteger a v) := by
  ext k i
  simp only [generatedAxisGlobalSignIntegerAction, generatedAxisGlobalOddTensorFactor,
    generatedAxisGlobalOddSignSpinInteger, generatedAxisGlobalOddSignSpatialInteger]
  rw [oddSign_Z_spatial]
  have hc := oddSign_code_products a (generatedAxisGlobalSpinLabelLow k) i
  linear_combination
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
        (generatedAxisGlobalSignLowCode a) 0
        (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a)
          (generatedAxisGlobalSpinLabelLow k)) (generatedAxisGlobalSpinLabelLow k)) *
      (u (generatedAxisGlobalTensorLowLabel
        (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a)
          (generatedAxisGlobalSpinLabelLow k))) -
      u (generatedAxisGlobalTensorHighLabel
        (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode a)
          (generatedAxisGlobalSpinLabelLow k)))) * v i * hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
