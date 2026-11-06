/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorCertificatesGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceTensorCalibration

/-! Exact initial and final retained packets and the genuine compact tensor anchor interface. All
  proof bodies are uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- Every retained initial spin coordinate is the exact delta vector, including all zeros. -/
theorem generatedTenth_source_delta_initial_spin (k : Fin 4096) :
    generatedTenthAxisLowerRecoverySourceDeltaTensorSpin 0 k = if k = 0 then 1 else 0 := by
  have h : ∀ k : Fin 4096, generatedTenthAxisLowerRecoverySourceDeltaTensorSpin 0 k = if k = 0 then
    1 else 0 := by
    decide +kernel
  exact h k

/-- Every physical initial coordinate is the exact original unit vector. -/
theorem generatedTenth_source_delta_initial_spatial (i : Fin 24) :
    generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial 0 i = if i = 0 then 1 else 0 := by
  have h : ∀ i : Fin 24, generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial 0 i = if i = 0 then
    1 else 0 := by
    decide +kernel
  exact h i

/-- The actual physical spin vector with label zero is the zero binary vector. -/
theorem generatedTenth_source_delta_golay_zero :
    golayLabelCoefficients (0 : Fin 4096) = (0 : SpinIndex) := by
  funext i
  have h : ∀ i : Fin 12, golayLabelCoefficients (0 : Fin 4096) i = 0 := by
    decide +kernel
  exact h i

/-- The complete initial integer packet equals the genuine physical delta tensor input. -/
theorem generatedTenth_source_delta_initial_packet :
    generatedTenthAxisLowerRecoverySourceDeltaTensorPacket 0 =
      generatedTenthAxisLowerRecoverySourceTensorAnchorInput := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  have hz : golayLabelCoefficients k = (0 : SpinIndex) ↔ k = 0 := by
    constructor
    · intro h
      apply golayLabelCoefficients_bijective.1
      exact h.trans generatedTenth_source_delta_golay_zero.symm
    · intro h
      rw [h, generatedTenth_source_delta_golay_zero]
  have hd : generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator 0 *
    generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator 0 = 1 := by
    decide +kernel
  unfold generatedTenthAxisLowerRecoverySourceDeltaTensorPacket
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient, hd]
  unfold generatedAxisGlobalOddTensorFactor
  rw [generatedTenth_source_delta_initial_spin, generatedTenth_source_delta_initial_spatial]
  simp [generatedTenthAxisLowerRecoverySourceTensorAnchorInput, Pi.single_apply,
    hz, div_eq_mul_inv]

/-- The final packet preserves the exact signed product numerator and normalization. -/
theorem generatedTenth_source_delta_final_packet_coefficient :
    generatedTenthAxisLowerRecoverySourceDeltaTensorPacket 7 (golayLabelCoefficients 0) 0 = -1 /
      (256 * Real.sqrt 2) := by
  have hn : generatedAxisGlobalOddTensorFactor (generatedTenthAxisLowerRecoverySourceDeltaTensorSpin
    7)
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial 7) 0 0 = -1 := by
    decide +kernel
  have hd : generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator 7 *
    generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator 7 = 256 := by
    decide +kernel
  unfold generatedTenthAxisLowerRecoverySourceDeltaTensorPacket
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient, hn, hd]
  norm_num

/-- A named actual compact spin factor prevents expansion during equality transport. -/
@[irreducible] private def sourceAnchorSpin : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val

/-- A named actual physical factor retains the original full source word. -/
@[irreducible] private def sourceAnchorSpatial : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) :=
  (generatedAxisGlobalFifthShortSpatialWord 2).val

private theorem sourceAnchorSpin_eq : sourceAnchorSpin =
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val := by
  unfold sourceAnchorSpin
  rfl

private theorem sourceAnchorSpatial_eq : sourceAnchorSpatial =
    (generatedAxisGlobalFifthShortSpatialWord 2).val := by
  unfold sourceAnchorSpatial
  rfl

private theorem sourceAnchorOperator_eq :
    coordinateGLTransport conwayTensorCoordinates
        (TensorProduct.congr sourceAnchorSpin sourceAnchorSpatial) =
      generatedTenthAxisLowerRecoverySourceCompactTensor := by
  have hc : generatedTenthAxisLowerRecoverySourceCompactTensor =
      coordinateGLTransport conwayTensorCoordinates
        (TensorProduct.congr (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
          (generatedAxisGlobalFifthShortSpatialWord 2).val) := rfl
  exact (congrArg₂ (fun (a : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (b : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) =>
      coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr a b))
    sourceAnchorSpin_eq sourceAnchorSpatial_eq).trans hc.symm

/-- Coordinate transport of a variable rank-one tensor retains both factors. -/
private theorem generatedTenth_source_delta_tensor_factors_generic
    (a : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (b : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) (u : SpinSpace) (v : Fin 24 → ℝ) :
    coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr a b)
        (fun t i => u t * v i) = fun t i => a u t * b v i := by
  have he : conwayTensorCoordinates (u ⊗ₜ[ℝ] v) = fun t i => u t * v i := by
    funext t i
    exact conwayTensorCoordinates_tmul u v t i
  rw [← he]
  simp only [coordinateGLTransport_apply, LinearEquiv.symm_apply_apply,
    TensorProduct.congr_tmul]
  funext t i
  exact conwayTensorCoordinates_tmul _ _ t i

/-- The genuine compact tensor operator acts on rank-one physical coordinates by its two factors. -/
theorem generatedTenth_source_delta_compact_tensor_factors (u : SpinSpace) (v : Fin 24 → ℝ) :
    generatedTenthAxisLowerRecoverySourceCompactTensor (fun t i => u t * v i) =
      fun t i => (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val u t *
        (generatedAxisGlobalFifthShortSpatialWord 2).val v i := by
  rw [← sourceAnchorOperator_eq, ← sourceAnchorSpin_eq, ← sourceAnchorSpatial_eq]
  exact generatedTenth_source_delta_tensor_factors_generic
    sourceAnchorSpin sourceAnchorSpatial u v

/-- Variable compact factors with both exact coefficients determine the signed anchor. -/
private theorem generatedTenth_source_delta_compact_anchor_generic
    (a : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (b : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hspin : a (Pi.single (0 : SpinIndex) (1 : ℝ)) (golayLabelCoefficients 0) = 1 / 64)
    (hspatial : b (Pi.single (0 : Fin 24) (1 : ℝ)) 0 = -1 / 4) :
    coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr a b)
      (fun t i => (Pi.single (0 : SpinIndex) (1 : ℝ) : SpinSpace) t *
        (Pi.single (0 : Fin 24) ((Real.sqrt 2)⁻¹) : Fin 24 → ℝ) i)
      (golayLabelCoefficients 0) 0 = -1 / (256 * Real.sqrt 2) := by
  have hv : (Pi.single (0 : Fin 24) ((Real.sqrt 2)⁻¹) : Fin 24 → ℝ) =
      (Real.sqrt 2)⁻¹ • Pi.single (0 : Fin 24) (1 : ℝ) := by
    funext i
    simp [Pi.single_apply]
  rw [generatedTenth_source_delta_tensor_factors_generic, hv, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hspin, hspatial]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

/-- These are compact and explicit spatial operators; no chosen source-fiber spin sign is fixed.
The two genuine coefficient obligations stay explicit until independently proved. -/
theorem generatedTenth_source_delta_compact_tensor_anchor_of_factors
    (hspin : (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
      (Pi.single (0 : SpinIndex) (1 : ℝ)) (golayLabelCoefficients 0) = 1 / 64)
    (hspatial : (generatedAxisGlobalFifthShortSpatialWord 2).val
      (Pi.single (0 : Fin 24) (1 : ℝ)) 0 = -1 / 4) :
    generatedTenthAxisLowerRecoverySourceCompactTensor
      generatedTenthAxisLowerRecoverySourceTensorAnchorInput
      (golayLabelCoefficients 0) 0 = -1 / (256 * Real.sqrt 2) := by
  have ha : sourceAnchorSpin (Pi.single (0 : SpinIndex) (1 : ℝ))
      (golayLabelCoefficients 0) = 1 / 64 := by
    exact (congrArg (fun a : SpinSpace ≃ₗ[ℝ] SpinSpace =>
      a (Pi.single (0 : SpinIndex) (1 : ℝ)) (golayLabelCoefficients 0))
      sourceAnchorSpin_eq).trans hspin
  have hb : sourceAnchorSpatial (Pi.single (0 : Fin 24) (1 : ℝ)) 0 = -1 / 4 := by
    exact (congrArg (fun b : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) =>
      b (Pi.single (0 : Fin 24) (1 : ℝ)) 0) sourceAnchorSpatial_eq).trans hspatial
  rw [← sourceAnchorOperator_eq]
  unfold generatedTenthAxisLowerRecoverySourceTensorAnchorInput
  exact generatedTenth_source_delta_compact_anchor_generic
    sourceAnchorSpin sourceAnchorSpatial ha hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
