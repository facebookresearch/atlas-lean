/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-sixteen candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeSixteenForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeSixteenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeSixteenInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeSixteenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSixteenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSixteenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSixteenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSixteenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSixteenForwardPacket_parts :
    monsterNortonCodeSixteenForwardPacket =
      monsterNortonCodeSixteenForwardShort + monsterNortonCodeSixteenForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeSixteenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSixteenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSixteenForwardSpinCoefficient
      monsterNortonCodeSixteenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeSixteenForwardSpinLabel i))
    monsterNortonCodeSixteenForwardColumns
    (fun i => (monsterNortonCodeSixteenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSixteenForwardLeech (monsterNortonCodeSixteenForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSixteenForwardLeech_sparse] at ht
  rw [monsterNortonCodeSixteenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeSixteenForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeSixteenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSixteenForwardTensorIndex p).1
        (monsterNortonCodeSixteenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSixteenForwardTensorCoefficient,
    monsterNortonCodeSixteenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeSixteenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSixteenInversePacket_parts :
    monsterNortonCodeSixteenInversePacket =
      monsterNortonCodeSixteenInverseShort + monsterNortonCodeSixteenInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeSixteenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSixteenInverseSpinCoefficient
      monsterNortonCodeSixteenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i))
    monsterNortonCodeSixteenInverseColumns
    (fun i => (monsterNortonCodeSixteenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSixteenInverseLeech (monsterNortonCodeSixteenInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSixteenInverseLeech_sparse] at ht
  rw [monsterNortonCodeSixteenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeSixteenInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeSixteenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSixteenInverseTensorIndex p).1
        (monsterNortonCodeSixteenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSixteenInverseTensorCoefficient,
    monsterNortonCodeSixteenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeSixteenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
