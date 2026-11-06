/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-nine candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeNineForwardShort : GriessSpace :=
  ∑ p : Fin 32 × Fin 8, ((monsterNortonCodeNineForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeNineInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeNineInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeNineInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeNineForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeNineForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeNineInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeNineInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeNineForwardPacket_parts :
    monsterNortonCodeNineForwardPacket =
      monsterNortonCodeNineForwardShort + monsterNortonCodeNineForwardTensor := by
  have hs : (∑ i : Fin 64, (monsterNortonCodeNineForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeNineForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeNineForwardSpinCoefficient
      monsterNortonCodeNineForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 64 => golayLabelCoefficients (monsterNortonCodeNineForwardSpinLabel i))
    monsterNortonCodeNineForwardColumns
    (fun i => (monsterNortonCodeNineForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeNineForwardLeech (monsterNortonCodeNineForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeNineForwardLeech_sparse] at ht
  rw [monsterNortonCodeNineForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeNineForwardShort +
    (∑ p : Fin 64 × Fin 8, ((monsterNortonCodeNineForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeNineForwardTensorIndex p).1
        (monsterNortonCodeNineForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeNineForwardTensorCoefficient,
    monsterNortonCodeNineForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeNineForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeNineInversePacket_parts :
    monsterNortonCodeNineInversePacket =
      monsterNortonCodeNineInverseShort + monsterNortonCodeNineInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeNineInverseSpinCoefficient
      monsterNortonCodeNineInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel i))
    monsterNortonCodeNineInverseColumns
    (fun i => (monsterNortonCodeNineInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeNineInverseLeech (monsterNortonCodeNineInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeNineInverseLeech_sparse] at ht
  rw [monsterNortonCodeNineInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeNineInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeNineInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeNineInverseTensorIndex p).1
        (monsterNortonCodeNineInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeNineInverseTensorCoefficient,
    monsterNortonCodeNineInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeNineInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
