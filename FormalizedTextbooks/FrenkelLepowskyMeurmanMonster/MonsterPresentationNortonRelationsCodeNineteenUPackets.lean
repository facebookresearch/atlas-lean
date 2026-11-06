/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-nineteen candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeNineteenForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeNineteenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeNineteenInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeNineteenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeNineteenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeNineteenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeNineteenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeNineteenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeNineteenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeNineteenForwardPacket_parts :
    monsterNortonCodeNineteenForwardPacket =
      monsterNortonCodeNineteenForwardShort + monsterNortonCodeNineteenForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineteenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeNineteenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeNineteenForwardSpinCoefficient
      monsterNortonCodeNineteenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeNineteenForwardSpinLabel i))
    monsterNortonCodeNineteenForwardColumns
    (fun i => (monsterNortonCodeNineteenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeNineteenForwardLeech (monsterNortonCodeNineteenForwardColumns
      j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeNineteenForwardLeech_sparse] at ht
  rw [monsterNortonCodeNineteenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeNineteenForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeNineteenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeNineteenForwardTensorIndex p).1
        (monsterNortonCodeNineteenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeNineteenForwardTensorCoefficient,
    monsterNortonCodeNineteenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeNineteenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeNineteenInversePacket_parts :
    monsterNortonCodeNineteenInversePacket =
      monsterNortonCodeNineteenInverseShort + monsterNortonCodeNineteenInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineteenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeNineteenInverseSpinCoefficient
      monsterNortonCodeNineteenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel i))
    monsterNortonCodeNineteenInverseColumns
    (fun i => (monsterNortonCodeNineteenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeNineteenInverseLeech (monsterNortonCodeNineteenInverseColumns
      j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeNineteenInverseLeech_sparse] at ht
  rw [monsterNortonCodeNineteenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeNineteenInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeNineteenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeNineteenInverseTensorIndex p).1
        (monsterNortonCodeNineteenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeNineteenInverseTensorCoefficient,
    monsterNortonCodeNineteenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeNineteenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
