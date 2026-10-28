/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-seventeen candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeSeventeenForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeSeventeenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeSeventeenInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSeventeenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSeventeenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSeventeenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSeventeenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSeventeenForwardPacket_parts :
    monsterNortonCodeSeventeenForwardPacket =
      monsterNortonCodeSeventeenForwardShort + monsterNortonCodeSeventeenForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeSeventeenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSeventeenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSeventeenForwardSpinCoefficient
      monsterNortonCodeSeventeenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeSeventeenForwardSpinLabel i))
    monsterNortonCodeSeventeenForwardColumns
    (fun i => (monsterNortonCodeSeventeenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSeventeenForwardLeech
      (monsterNortonCodeSeventeenForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSeventeenForwardLeech_sparse] at ht
  rw [monsterNortonCodeSeventeenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeSeventeenForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeSeventeenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSeventeenForwardTensorIndex p).1
        (monsterNortonCodeSeventeenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSeventeenForwardTensorCoefficient,
    monsterNortonCodeSeventeenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeSeventeenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSeventeenInversePacket_parts :
    monsterNortonCodeSeventeenInversePacket =
      monsterNortonCodeSeventeenInverseShort + monsterNortonCodeSeventeenInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeSeventeenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSeventeenInverseSpinCoefficient
      monsterNortonCodeSeventeenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i))
    monsterNortonCodeSeventeenInverseColumns
    (fun i => (monsterNortonCodeSeventeenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSeventeenInverseLeech
      (monsterNortonCodeSeventeenInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSeventeenInverseLeech_sparse] at ht
  rw [monsterNortonCodeSeventeenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeSeventeenInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeSeventeenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSeventeenInverseTensorIndex p).1
        (monsterNortonCodeSeventeenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSeventeenInverseTensorCoefficient,
    monsterNortonCodeSeventeenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeSeventeenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
