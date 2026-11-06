/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneShortUCertificate

/-! Complete short/tensor decompositions of the original normalized code-twentyone candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete short part of the actual normalized forward candidate. -/
def monsterNortonCodeTwentyOneForwardShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeTwentyOneForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex p)

/-- The complete short part of the actual normalized inverse candidate. -/
def monsterNortonCodeTwentyOneInverseShort : GriessSpace :=
  ∑ p : Fin 8 × Fin 32, ((monsterNortonCodeTwentyOneInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyOneInverseShortIndex p)

/-- The original forward tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTwentyOneForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTwentyOneForwardLeech j : ℝ))))

/-- The original inverse tensor packet, retaining its full spin and physical factors. -/
def monsterNortonCodeTwentyOneInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger ⊗ₜ[ℝ]
      (fun j => (monsterNortonCodeTwentyOneInverseLeech j : ℝ))))

/-- The whole forward candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTwentyOneForwardPacket_parts :
    monsterNortonCodeTwentyOneForwardPacket =
      monsterNortonCodeTwentyOneForwardShort + monsterNortonCodeTwentyOneForwardTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyOneForwardSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTwentyOneForwardSpinCoefficient
      monsterNortonCodeTwentyOneForwardSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel i))
    monsterNortonCodeTwentyOneForwardColumns
    (fun i => (monsterNortonCodeTwentyOneForwardSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTwentyOneForwardLeech
      (monsterNortonCodeTwentyOneForwardColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTwentyOneForwardLeech_sparse] at ht
  rw [monsterNortonCodeTwentyOneForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyOneForwardShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeTwentyOneForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyOneForwardTensorIndex p).1
        (monsterNortonCodeTwentyOneForwardTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTwentyOneForwardTensorCoefficient,
    monsterNortonCodeTwentyOneForwardTensorIndex, Int.cast_mul,
    monsterNortonCodeTwentyOneForwardTensor] using ht

/-- The whole inverse candidate equals its genuine short part plus its genuine product tensor. -/
theorem monsterNortonCodeTwentyOneInversePacket_parts :
    monsterNortonCodeTwentyOneInversePacket =
      monsterNortonCodeTwentyOneInverseShort + monsterNortonCodeTwentyOneInverseTensor := by
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyOneInverseSpinCoefficient i : ℝ) •
      (Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel i)) 1 :
        SpinSpace)) = nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger :=
    (monsterNortonUIntegerEmbed_packet monsterNortonCodeTwentyOneInverseSpinCoefficient
      monsterNortonCodeTwentyOneInverseSpinLabel).symm
  have ht := monsterNortonSparseTensor_normalized
    (fun i : Fin 16 => golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel i))
    monsterNortonCodeTwentyOneInverseColumns
    (fun i => (monsterNortonCodeTwentyOneInverseSpinCoefficient i : ℝ))
    (fun j => (monsterNortonCodeTwentyOneInverseLeech
      (monsterNortonCodeTwentyOneInverseColumns j) : ℝ))
    (32 * Real.sqrt 2)
  rw [hs, monsterNortonCodeTwentyOneInverseLeech_sparse] at ht
  rw [monsterNortonCodeTwentyOneInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyOneInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeTwentyOneInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyOneInverseTensorIndex p).1
        (monsterNortonCodeTwentyOneInverseTensorIndex p).2) = _
  congr 1
  simpa only [monsterNortonCodeTwentyOneInverseTensorCoefficient,
    monsterNortonCodeTwentyOneInverseTensorIndex, Int.cast_mul,
    monsterNortonCodeTwentyOneInverseTensor] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
