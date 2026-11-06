/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-twenty candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeTwentyForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeTwentyForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeTwentyInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTwentyForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTwentyForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTwentyInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTwentyInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTwentyForwardPacket_parts :
    monsterNortonCodeTwentyForwardPacket =
      monsterNortonCodeTwentyForwardShort + monsterNortonCodeTwentyForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTwentyForwardSpinCoefficient
      monsterNortonCodeTwentyForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeTwentyForwardSpinLabel i))
    monsterNortonCodeTwentyForwardColumns
    (fun i => (monsterNortonCodeTwentyForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTwentyForwardLeech (monsterNortonCodeTwentyForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTwentyForwardLeech_sparse] at ht
  rw [monsterNortonCodeTwentyForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeTwentyForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyForwardTensorIndex p).1
        (monsterNortonCodeTwentyForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTwentyForwardTensorCoefficient,
    monsterNortonCodeTwentyForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeTwentyForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTwentyInversePacket_parts :
    monsterNortonCodeTwentyInversePacket =
      monsterNortonCodeTwentyInverseShort + monsterNortonCodeTwentyInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTwentyInverseSpinCoefficient
      monsterNortonCodeTwentyInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i))
    monsterNortonCodeTwentyInverseColumns
    (fun i => (monsterNortonCodeTwentyInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTwentyInverseLeech (monsterNortonCodeTwentyInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTwentyInverseLeech_sparse] at ht
  rw [monsterNortonCodeTwentyInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeTwentyInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyInverseTensorIndex p).1
        (monsterNortonCodeTwentyInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTwentyInverseTensorCoefficient,
    monsterNortonCodeTwentyInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeTwentyInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
