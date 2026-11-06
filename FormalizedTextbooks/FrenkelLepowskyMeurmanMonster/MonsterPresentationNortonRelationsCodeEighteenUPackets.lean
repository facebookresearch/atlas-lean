/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-eighteen candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeEighteenForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeEighteenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeEighteenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeEighteenInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeEighteenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeEighteenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeEighteenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeEighteenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeEighteenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeEighteenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeEighteenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeEighteenForwardPacket_parts :
    monsterNortonCodeEighteenForwardPacket =
      monsterNortonCodeEighteenForwardShort + monsterNortonCodeEighteenForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeEighteenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeEighteenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeEighteenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeEighteenForwardSpinCoefficient
      monsterNortonCodeEighteenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeEighteenForwardSpinLabel i))
    monsterNortonCodeEighteenForwardColumns
    (fun i => (monsterNortonCodeEighteenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeEighteenForwardLeech (monsterNortonCodeEighteenForwardColumns
      j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeEighteenForwardLeech_sparse] at ht
  rw [monsterNortonCodeEighteenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeEighteenForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeEighteenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeEighteenForwardTensorIndex p).1
        (monsterNortonCodeEighteenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeEighteenForwardTensorCoefficient,
    monsterNortonCodeEighteenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeEighteenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeEighteenInversePacket_parts :
    monsterNortonCodeEighteenInversePacket =
      monsterNortonCodeEighteenInverseShort + monsterNortonCodeEighteenInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeEighteenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeEighteenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeEighteenInverseSpinCoefficient
      monsterNortonCodeEighteenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeEighteenInverseSpinLabel i))
    monsterNortonCodeEighteenInverseColumns
    (fun i => (monsterNortonCodeEighteenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeEighteenInverseLeech (monsterNortonCodeEighteenInverseColumns
      j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeEighteenInverseLeech_sparse] at ht
  rw [monsterNortonCodeEighteenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeEighteenInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeEighteenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeEighteenInverseTensorIndex p).1
        (monsterNortonCodeEighteenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeEighteenInverseTensorCoefficient,
    monsterNortonCodeEighteenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeEighteenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
