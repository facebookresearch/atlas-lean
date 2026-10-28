/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSpreadTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSectionTransport

/-! Transport of entire intrinsic marking families, with root-range preservation explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Preservation of the genuine destination root range pulls back to the whole recovered range. -/
theorem generatedNinth_affine_root_preserved_of_conjugate (g : leechIsomSubgroup)
    (hroot : generatedAxisE8FrameRootEmbedding.range.map
      (leechModTwoAction
        (generatedNinthAffineTransport * g * generatedNinthAffineTransport⁻¹)).toLinearMap =
      generatedAxisE8FrameRootEmbedding.range) :
    generatedNinthAffineRootClassRange.map (leechModTwoAction g).toLinearMap =
      generatedNinthAffineRootClassRange := by
  change g • generatedNinthAffineRootClassRange = generatedNinthAffineRootClassRange
  apply (MulAction.injective generatedNinthAffineTransport)
  have ht : generatedNinthAffineTransport • generatedNinthAffineRootClassRange =
      generatedAxisE8FrameRootEmbedding.range := generatedNinth_affine_root_class_range_transport
  calc
    generatedNinthAffineTransport • (g • generatedNinthAffineRootClassRange) =
        (generatedNinthAffineTransport * g * generatedNinthAffineTransport⁻¹) •
          (generatedNinthAffineTransport • generatedNinthAffineRootClassRange) := by
      simp only [mul_smul, inv_smul_smul]
    _ = generatedAxisE8FrameRootEmbedding.range := by rw [ht]; exact hroot
    _ = generatedNinthAffineTransport • generatedNinthAffineRootClassRange := ht.symm

/-- Preserving the actual markings and root range fixes the entire transported spread. -/
theorem generatedNinth_affine_spread_conjugate_fixed (g : leechIsomSubgroup)
    (hR : generatedNinthAffineRootClassRange.map (leechModTwoAction g).toLinearMap =
      generatedNinthAffineRootClassRange)
    (hC : leechModTwoAction g '' generatedNinthMarkedShortClasses =
      generatedNinthMarkedShortClasses) :
    (generatedNinthAffineTransport * g * generatedNinthAffineTransport⁻¹) •
      generatedNinthAffineDestinationCarrier = generatedNinthAffineDestinationCarrier := by
  classical
  have hf := generatedNinth_affine_direction_family_preserved (leechModTwoAction g) hR hC
  have ht := generatedNinth_affine_spread_family_transport
  change generatedNinthAffineTransport • Set.range generatedNinthAffineDirectionClassSpace =
    (generatedNinthAffineDestinationCarrier : Set (Submodule (ZMod 2) LeechModTwo)) at ht
  change g • Set.range generatedNinthAffineDirectionClassSpace =
    Set.range generatedNinthAffineDirectionClassSpace at hf
  apply Finset.coe_injective
  rw [Finset.coe_smul_finset]
  rw [← ht]
  simp only [mul_smul, inv_smul_smul, hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
