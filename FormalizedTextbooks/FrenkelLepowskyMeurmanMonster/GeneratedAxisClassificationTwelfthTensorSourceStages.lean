/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerStages

/-! Every genuine Fifth normalization stage separates into original spin and physical factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full spin numerator after the original monomial and source-sign operations. -/
def generatedTwelfthTensorSourceSignedSpin (k : Fin 14) (j : Fin 7)
    (u : Fin 4096 → ℤ) : Fin 4096 → ℤ :=
  generatedTwelfthTensorSignSpinInteger (generatedAxisGlobalFifthShortNormalizationSigns k j)
    (generatedAxisGlobalOddMonomialSpinInteger
      (generatedAxisGlobalFifthShortNormalizationWords k j) u)

/-- The full physical numerator after those same genuine original source operations. -/
def generatedTwelfthTensorSourceSignedSpatial (k : Fin 14) (j : Fin 7)
    (v : Fin 24 → ℤ) : Fin 24 → ℤ :=
  generatedTwelfthTensorSignSpatialInteger (generatedAxisGlobalFifthShortNormalizationSigns k j)
    (generatedAxisGlobalOddMonomialSpatialInteger
      (generatedAxisGlobalFifthShortNormalizationWords k j) v)

/-- The complete original spin numerator after the genuine optional Xi operation. -/
def generatedTwelfthTensorSourceStageSpin (k : Fin 14) (j : Fin 7)
    (u : Fin 4096 → ℤ) : Fin 4096 → ℤ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then
    generatedAxisGlobalOddXiSpinInteger (generatedTwelfthTensorSourceSignedSpin k j u)
  else generatedTwelfthTensorSourceSignedSpin k j u

/-- The complete original physical numerator after the identical genuine optional Xi operation. -/
def generatedTwelfthTensorSourceStageSpatial (k : Fin 14) (j : Fin 7)
    (v : Fin 24 → ℤ) : Fin 24 → ℤ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then
    generatedAxisGlobalOddXiSpatialInteger (generatedTwelfthTensorSourceSignedSpatial k j v)
  else generatedTwelfthTensorSourceSignedSpatial k j v

/-- The original spin denominator keeps both genuine sign and Xi normalizations. -/
def generatedTwelfthTensorSourceStageSpinDenominator (k : Fin 14) (j : Fin 7) (D : ℕ) : ℕ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then 8 * (2 * D) else 2 * D

/-- The original physical denominator keeps the true Xi spatial normalization. -/
def generatedTwelfthTensorSourceStageSpatialDenominator (k : Fin 14) (j : Fin 7) (D : ℕ) : ℕ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then 2 * D else D

/-- The two factor denominators multiply to exactly the original entire tensor denominator. -/
theorem generatedTwelfth_tensor_source_stage_denominator (k : Fin 14) (j : Fin 7) (Ds Dv : ℕ) :
    generatedTwelfthTensorSourceStageSpinDenominator k j Ds *
        generatedTwelfthTensorSourceStageSpatialDenominator k j Dv =
      generatedAxisGlobalFifthIntegerStageDenominator k j (Ds * Dv) := by
  unfold generatedTwelfthTensorSourceStageSpinDenominator
    generatedTwelfthTensorSourceStageSpatialDenominator
    generatedAxisGlobalFifthIntegerStageDenominator
  cases generatedAxisGlobalFifthShortNormalizationXi k j <;> simp <;> ring

/-- Every full normalization stage factors, retaining all original tensor coordinates. -/
theorem generatedTwelfth_tensor_source_stage_integer_factor (k : Fin 14) (j : Fin 7)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalFifthIntegerStage k j (generatedAxisGlobalOddTensorFactor u v) =
      generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceStageSpin k j u)
        (generatedTwelfthTensorSourceStageSpatial k j v) := by
  unfold generatedAxisGlobalFifthIntegerStage generatedAxisGlobalFifthIntegerSignedStage
  rw [generatedAxisGlobalOddMonomialInteger_factor, generatedTwelfth_tensor_sign_integer_factor]
  unfold generatedTwelfthTensorSourceStageSpin generatedTwelfthTensorSourceStageSpatial
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [↓reduceIte]
    exact generatedAxisGlobalOddXiInteger_factor
      (generatedTwelfthTensorSourceSignedSpin k j u)
      (generatedTwelfthTensorSourceSignedSpatial k j v)

/-- Each entire original local stage acts exactly on the genuine separated physical factors. -/
theorem generatedTwelfth_tensor_source_stage_packet (k : Fin 14) (j : Fin 7)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (Ds Dv : ℕ) :
    localTensorRepresentation (generatedAxisGlobalFifthShortNormalizationFiber k j)
      (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) (Ds * Dv)) =
        generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceStageSpin k j u)
            (generatedTwelfthTensorSourceStageSpatial k j v))
          (generatedTwelfthTensorSourceStageSpinDenominator k j Ds *
            generatedTwelfthTensorSourceStageSpatialDenominator k j Dv) := by
  rw [generatedAxisGlobalFifthIntegerStage_packet,
    generatedTwelfth_tensor_source_stage_integer_factor,
    generatedTwelfth_tensor_source_stage_denominator]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
