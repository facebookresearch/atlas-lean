/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMonomialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitIntegralCertificates

/-! The checked integer and binary matrices are the genuine actual source isometry actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The certified original isometries act on the actual integral Leech basis as displayed. -/
theorem sixthFrameOrbit_monomial_basis (k : Fin 16) (z : Fin 24 → ℤ) :
    (sixthFrameOrbitMonomialIsometry k).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (sixthFrameOrbitIntegral k *ᵥ z)) := by
  ext i
  rw [sixthFrameOrbit_monomial_apply]
  have h : (leechBasisMatrix *ᵥ (sixthFrameOrbitIntegral k *ᵥ z)) i =
      sixthFrameOrbitSpatialSign k i * (leechBasisMatrix *ᵥ z)
        (sixthFrameOrbitSpatialInput k i) := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, sixthFrameOrbit_integral_check]
    simp only [mul_assoc]
    exact (Finset.mul_sum _ _ _).symm
  change (sixthFrameOrbitSpatialSign k i : ℝ) *
    (((leechBasisMatrix *ᵥ z) (sixthFrameOrbitSpatialInput k i) : ℝ) / Real.sqrt 8) =
      ((leechBasisMatrix *ᵥ (sixthFrameOrbitIntegral k *ᵥ z)) i : ℝ) / Real.sqrt 8
  rw [h, Int.cast_mul]
  ring


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
