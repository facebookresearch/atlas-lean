/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorSignFactors

/-! Complete integral tensor separation for every original source sign, including Omega. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual original physical coordinate sign of an arbitrary full source Golay label. -/
def generatedTwelfthTensorPhysicalSign (a : Fin 4096) (i : Fin 24) : ℤ :=
  generatedAxisGlobalIntSign (golayEncoder (golayLabelCoefficients a) i)

/-- The source Omega coordinate really encodes the entire all-one physical word. -/
theorem generatedTwelfth_tensor_omega_encoder :
    ∀ i : Fin 24, golayEncoder (Pi.single 11 1 : SpinIndex) i = 1 := by
  decide +kernel

/-- Every full source code keeps the Omega correction in its two original dictionary signs. -/
theorem generatedTwelfth_tensor_sign_code_products (a : Fin 4096) (e : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalCodeSign e i *
        generatedAxisGlobalCodeSign (generatedAxisGlobalSignInputCode a e) i =
      generatedTwelfthTensorPhysicalSign a i *
        generatedAxisGlobalIntSign (golayLabelCoefficients a 11) := by
  have h := congrArg (fun t => golayEncoder t i)
    (generatedAxisGlobalSignInputCode_translation a e)
  simp only [map_add, Pi.add_apply, map_smul, Pi.smul_apply,
    generatedTwelfth_tensor_omega_encoder, smul_eq_mul, mul_one] at h
  have hc : golayEncoder (generatedFifthSpinLow e) i +
      golayEncoder (generatedFifthSpinLow (generatedAxisGlobalSignInputCode a e)) i =
    golayEncoder (golayLabelCoefficients a) i + golayLabelCoefficients a 11 := by
    linear_combination (norm := skip) h
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]
    rfl
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, generatedAxisGlobalCodeSign_real,
    generatedTwelfthTensorPhysicalSign, generatedAxisGlobalIntSign_real]
  rw [← golayEncoder_low_qSign, ← golayEncoder_low_qSign]
  change qSign (golayEncoder (generatedFifthSpinLow e) i) *
    qSign (golayEncoder (generatedFifthSpinLow (generatedAxisGlobalSignInputCode a e)) i) = _
  rw [← qSign_add, hc, qSign_add]

/-- The full original lower source phase separates into its physical and symmetric spin signs. -/
theorem generatedTwelfth_tensor_sign_Z_physical (a : Fin 4096) (e : Fin 2048) (i : Fin 24) :
    qSign (generatedAxisGlobalSignZPhase a e i) =
      qSign (golayEncoder (golayLabelCoefficients a) i) *
        qSign (spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e))
          (golayLabelCoefficients a) +
          spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients a))
            (generatedFifthSpinLow e)) := by
  unfold generatedAxisGlobalSignZPhase
  rw [sourceWordTheta_polynomial, sourceWordTheta_polynomial]
  change qSign (spinDot (golayLabelCoefficients a)
    (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) +
    golayEncoder (golayLabelCoefficients a) i +
    spinDot (generatedFifthSpinLow e) (sourceCodeThetaPolynomial (golayLabelCoefficients a))) = _
  rw [spinDot_comm (golayLabelCoefficients a), spinDot_comm (generatedFifthSpinLow e)]
  simp only [qSign_add]
  ring

/-- All source Z phases have one genuine physical coordinate sign multiplying their spin phase. -/
theorem generatedTwelfth_tensor_sign_Z_factor (a : Fin 4096) (e : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e i) =
      generatedTwelfthTensorPhysicalSign a i * generatedTwelfthTensorPhysicalSign a 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e 0) := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, generatedTwelfthTensorPhysicalSign, generatedAxisGlobalIntSign_real]
  rw [generatedTwelfth_tensor_sign_Z_physical, generatedTwelfth_tensor_sign_Z_physical]
  rw [mul_assoc, ← mul_assoc (qSign (golayEncoder (golayLabelCoefficients a) 0)),
    qSign_sq, one_mul]

/-- The entire original four-input spin numerator, retaining the full source Omega label. -/
def generatedTwelfthTensorSignSpinInteger (a : Fin 4096) (u : Fin 4096 → ℤ)
    (k : Fin 4096) : ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedAxisGlobalIntSign (golayLabelCoefficients a 11) *
      generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a 0 d e) *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) +
    generatedTwelfthTensorPhysicalSign a 0 *
      generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e 0) *
      (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e))

/-- The entire original physical source sign acts on every coordinate of the spatial factor. -/
def generatedTwelfthTensorSignSpatialInteger (a : Fin 4096) (v : Fin 24 → ℤ)
    (i : Fin 24) : ℤ := generatedTwelfthTensorPhysicalSign a i * v i

/-- Every full source sign factors exactly, without omitting any physical tensor coefficient. -/
theorem generatedTwelfth_tensor_sign_integer_factor (a : Fin 4096)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalSignIntegerAction (generatedAxisGlobalOddTensorFactor u v) a 0 =
      generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSignSpinInteger a u)
        (generatedTwelfthTensorSignSpatialInteger a v) := by
  ext k i
  simp only [generatedAxisGlobalSignIntegerAction, generatedAxisGlobalOddTensorFactor,
    generatedTwelfthTensorSignSpinInteger, generatedTwelfthTensorSignSpatialInteger]
  rw [generatedTwelfth_tensor_sign_Z_factor]
  have hc := generatedTwelfth_tensor_sign_code_products a (generatedAxisGlobalSpinLabelLow k) i
  linear_combination
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a 0
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k))
        (generatedAxisGlobalSpinLabelLow k)) *
      (u (generatedAxisGlobalTensorLowLabel
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k))) -
        u (generatedAxisGlobalTensorHighLabel
          (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k)))) * v i * hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
