/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-seven candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeSevenForwardShort : GriessSpace :=
  ∑ p : Fin 32 × Fin 8, ((monsterNortonCodeSevenForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeSevenInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeSevenInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeSevenInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSevenForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSevenForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeSevenInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeSevenInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSevenForwardPacket_parts :
    monsterNortonCodeSevenForwardPacket =
      monsterNortonCodeSevenForwardShort + monsterNortonCodeSevenForwardTensor := by
  have hs : (∑ i : Fin 64, (monsterNortonCodeSevenForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSevenForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSevenForwardSpinCoefficient
      monsterNortonCodeSevenForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 64 => golayLabelCoefficients (monsterNortonCodeSevenForwardSpinLabel i))
    monsterNortonCodeSevenForwardColumns
    (fun i => (monsterNortonCodeSevenForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSevenForwardLeech (monsterNortonCodeSevenForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSevenForwardLeech_sparse] at ht
  rw [monsterNortonCodeSevenForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeSevenForwardShort +
    (∑ p : Fin 64 × Fin 8, ((monsterNortonCodeSevenForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSevenForwardTensorIndex p).1
        (monsterNortonCodeSevenForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSevenForwardTensorCoefficient,
    monsterNortonCodeSevenForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeSevenForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeSevenInversePacket_parts :
    monsterNortonCodeSevenInversePacket =
      monsterNortonCodeSevenInverseShort + monsterNortonCodeSevenInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeSevenInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeSevenInverseSpinCoefficient
      monsterNortonCodeSevenInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel i))
    monsterNortonCodeSevenInverseColumns
    (fun i => (monsterNortonCodeSevenInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeSevenInverseLeech (monsterNortonCodeSevenInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeSevenInverseLeech_sparse] at ht
  rw [monsterNortonCodeSevenInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeSevenInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeSevenInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeSevenInverseTensorIndex p).1
        (monsterNortonCodeSevenInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeSevenInverseTensorCoefficient,
    monsterNortonCodeSevenInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeSevenInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
