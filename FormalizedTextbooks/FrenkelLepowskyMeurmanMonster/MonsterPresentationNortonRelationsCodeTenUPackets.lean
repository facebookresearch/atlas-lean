/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized basis-ten candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeTenForwardShort : GriessSpace :=
  ∑ p : Fin 32 × Fin 8, ((monsterNortonCodeTenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeTenInverseShort : GriessSpace :=
  ∑ p : Fin 2 × Fin 128, ((monsterNortonCodeTenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTenForwardPacket_parts :
    monsterNortonCodeTenForwardPacket =
      monsterNortonCodeTenForwardShort + monsterNortonCodeTenForwardTensor := by
  have hs : (∑ i : Fin 64, (monsterNortonCodeTenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTenForwardSpinCoefficient
      monsterNortonCodeTenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 64 => golayLabelCoefficients (monsterNortonCodeTenForwardSpinLabel i))
    monsterNortonCodeTenForwardColumns
    (fun i => (monsterNortonCodeTenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTenForwardLeech (monsterNortonCodeTenForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTenForwardLeech_sparse] at ht
  rw [monsterNortonCodeTenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeTenForwardShort +
    (∑ p : Fin 64 × Fin 8, ((monsterNortonCodeTenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTenForwardTensorIndex p).1
        (monsterNortonCodeTenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTenForwardTensorCoefficient,
    monsterNortonCodeTenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeTenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTenInversePacket_parts :
    monsterNortonCodeTenInversePacket =
      monsterNortonCodeTenInverseShort + monsterNortonCodeTenInverseTensor := by
  have hs : (∑ i : Fin 4, (monsterNortonCodeTenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTenInverseSpinCoefficient
      monsterNortonCodeTenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 4 => golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i))
    monsterNortonCodeTenInverseColumns
    (fun i => (monsterNortonCodeTenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTenInverseLeech (monsterNortonCodeTenInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTenInverseLeech_sparse] at ht
  rw [monsterNortonCodeTenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeTenInverseShort +
    (∑ p : Fin 4 × Fin 1, ((monsterNortonCodeTenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTenInverseTensorIndex p).1
        (monsterNortonCodeTenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTenInverseTensorCoefficient,
    monsterNortonCodeTenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeTenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
