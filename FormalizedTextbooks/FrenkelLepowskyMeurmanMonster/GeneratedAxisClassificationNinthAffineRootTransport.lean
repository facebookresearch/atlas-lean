/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineTransportAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineFiberRecovery
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsIncidence

/-! Original transport of the entire recovered quotient-section range to the genuine
original eight-root E8 range. All binary identities derive from the actual lattice word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original selected-section root coordinates of the eight transported recovered directions. -/
def generatedNinthAffineRootTransportMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun j k => generatedAxisE8FrameLabelBits (generatedNinthAffineTransportRootLabels k) j

/-- A proposed inverse in the actual original eight-root coordinate basis. -/
def generatedNinthAffineRootTransportInverse : Matrix (Fin 8) (Fin 8) (ZMod 2) := ![
    ![0, 1, 1, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1],
    ![1, 0, 0, 1, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 1, 1, 1],
    ![0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 1, 1, 1, 1]]

/-- Both original eight-coordinate matrix products certify a genuine basis change. -/
theorem generatedNinth_affine_root_transport_inverse :
    generatedNinthAffineRootTransportMatrix * generatedNinthAffineRootTransportInverse = 1 ∧
      generatedNinthAffineRootTransportInverse * generatedNinthAffineRootTransportMatrix = 1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Bind all192 source-direction bits through the actual full transport matrix.
/-- Actual binary transport sends all eight recovered directions to the specified original roots. -/
theorem generatedNinth_affine_root_transport_certificate :
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *
      generatedNinthAffineRootMatrix =
        generatedFifthFrameBinaryMatrix * generatedNinthAffineRootTransportMatrix := by
  decide +kernel

/-- Every recovered quotient direction has its actual original eight-root transport coordinates. -/
theorem generatedNinth_affine_root_class_transport (a : Fin 8 → ZMod 2) :
    leechModTwoAction generatedNinthAffineTransport (generatedNinthAffineRootClassMap a) =
      generatedAxisE8FrameRootEmbedding (generatedNinthAffineRootTransportMatrix *ᵥ a) := by
  apply leechHyperbolicCoordinates.injective
  rw [← leechBinaryAction_coordinates]
  change leechBinaryAction generatedNinthAffineTransport
      (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _)) =
    leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    generatedNinth_affine_transport_binary_action]
  change sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
      (generatedNinthAffineRootMatrix *ᵥ a) =
    generatedFifthFrameBinaryMatrix *ᵥ (generatedNinthAffineRootTransportMatrix *ᵥ a)
  rw [Matrix.mulVec_mulVec, generatedNinth_affine_root_transport_certificate,
    Matrix.mulVec_mulVec]

/-- The genuine full transport identifies the entire recovered range with the original E8 range. -/
theorem generatedNinth_affine_root_class_range_transport :
    generatedNinthAffineRootClassRange.map
      (leechModTwoAction generatedNinthAffineTransport).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range := by
  ext u
  constructor
  · rintro ⟨v, ⟨a, rfl⟩, rfl⟩
    exact ⟨generatedNinthAffineRootTransportMatrix *ᵥ a,
      (generatedNinth_affine_root_class_transport a).symm⟩
  · rintro ⟨a, rfl⟩
    let b := generatedNinthAffineRootTransportInverse *ᵥ a
    refine ⟨generatedNinthAffineRootClassMap b, ⟨b, rfl⟩, ?_⟩
    change leechModTwoAction generatedNinthAffineTransport
      (generatedNinthAffineRootClassMap b) = generatedAxisE8FrameRootEmbedding a
    rw [generatedNinth_affine_root_class_transport]
    have he : generatedNinthAffineRootTransportMatrix *ᵥ b = a := by
      change generatedNinthAffineRootTransportMatrix *ᵥ
        (generatedNinthAffineRootTransportInverse *ᵥ a) = a
      rw [Matrix.mulVec_mulVec, generatedNinth_affine_root_transport_inverse.1,
        Matrix.one_mulVec]
    rw [he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
