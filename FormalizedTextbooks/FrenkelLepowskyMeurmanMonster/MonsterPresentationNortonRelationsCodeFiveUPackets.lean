/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-five candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeFiveForwardShort : GriessSpace :=
  ∑ p : Fin 32 × Fin 8, ((monsterNortonCodeFiveForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeFiveInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeFiveInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeFiveInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeFiveForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeFiveForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeFiveInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeFiveInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeFiveForwardPacket_parts :
    monsterNortonCodeFiveForwardPacket =
      monsterNortonCodeFiveForwardShort + monsterNortonCodeFiveForwardTensor := by
  have hs : (∑ i : Fin 64, (monsterNortonCodeFiveForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeFiveForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeFiveForwardSpinCoefficient
      monsterNortonCodeFiveForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 64 => golayLabelCoefficients (monsterNortonCodeFiveForwardSpinLabel i))
    monsterNortonCodeFiveForwardColumns
    (fun i => (monsterNortonCodeFiveForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeFiveForwardLeech (monsterNortonCodeFiveForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeFiveForwardLeech_sparse] at ht
  rw [monsterNortonCodeFiveForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeFiveForwardShort +
    (∑ p : Fin 64 × Fin 8, ((monsterNortonCodeFiveForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeFiveForwardTensorIndex p).1
        (monsterNortonCodeFiveForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeFiveForwardTensorCoefficient,
    monsterNortonCodeFiveForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeFiveForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeFiveInversePacket_parts :
    monsterNortonCodeFiveInversePacket =
      monsterNortonCodeFiveInverseShort + monsterNortonCodeFiveInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeFiveInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeFiveInverseSpinCoefficient
      monsterNortonCodeFiveInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel i))
    monsterNortonCodeFiveInverseColumns
    (fun i => (monsterNortonCodeFiveInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeFiveInverseLeech (monsterNortonCodeFiveInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeFiveInverseLeech_sparse] at ht
  rw [monsterNortonCodeFiveInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeFiveInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeFiveInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeFiveInverseTensorIndex p).1
        (monsterNortonCodeFiveInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeFiveInverseTensorCoefficient,
    monsterNortonCodeFiveInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeFiveInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
