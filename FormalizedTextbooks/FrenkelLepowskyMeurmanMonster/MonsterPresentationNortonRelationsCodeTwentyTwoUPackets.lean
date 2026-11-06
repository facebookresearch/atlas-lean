/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinPackets

/-! Whole short and tensor decompositions of the actual basis22 mixed candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete normalized forward short part. -/
def monsterNortonCodeTwentyTwoForwardShort : GriessSpace :=
  ∑ p : Fin 32 × Fin 16, ((monsterNortonCodeTwentyTwoForwardShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex p)

/-- The complete normalized inverse short part. -/
def monsterNortonCodeTwentyTwoInverseShort : GriessSpace :=
  ∑ p : Fin 16 × Fin 32, ((monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2 : ℝ) / 32) •
    monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex p)

/-- The full forward tensor retains every original spin row and physical column. -/
def monsterNortonCodeTwentyTwoForwardTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • ∑ s : Fin 64,
    monsterNortonTensorLift (conwayTensorCoordinates
      ((Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel s)) 1 :
        SpinSpace) ⊗ₜ[ℝ] monsterNortonCodeTwentyTwoLeechRow s))

/-- The full inverse tensor retains its four spin entries at each original physical column. -/
def monsterNortonCodeTwentyTwoInverseTensor : GriessSpace :=
  (1 / (32 * Real.sqrt 2) : ℝ) • ∑ k : Fin 16,
    monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k) ⊗ₜ[ℝ]
        (Pi.single (monsterNortonCodeTwentyTwoInverseColumns k) 1 : Fin 24 → ℝ)))

/-- The actual forward candidate is its whole short part plus its full tensor part. -/
theorem monsterNortonCodeTwentyTwoForwardPacket_parts :
    monsterNortonCodeTwentyTwoForwardPacket =
      monsterNortonCodeTwentyTwoForwardShort + monsterNortonCodeTwentyTwoForwardTensor := by
  rw [monsterNortonCodeTwentyTwoForwardPacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyTwoForwardShort +
    (∑ p : Fin 64 × Fin 16, ((monsterNortonCodeTwentyTwoForwardTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyTwoForwardTensorIndex p).1
        (monsterNortonCodeTwentyTwoForwardTensorIndex p).2) = _
  congr 1
  unfold monsterNortonCodeTwentyTwoForwardTensor
  simp_rw [← monsterNortonCodeTwentyTwoLeechRow_sparse]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul,
    Finset.smul_sum, smul_smul, monsterNortonCodeTwentyTwoForwardTensorCoefficient,
    monsterNortonCodeTwentyTwoForwardTensorIndex, monsterNortonTensorUnit_product]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The actual inverse candidate is its whole short part plus its full tensor part. -/
theorem monsterNortonCodeTwentyTwoInversePacket_parts :
    monsterNortonCodeTwentyTwoInversePacket =
      monsterNortonCodeTwentyTwoInverseShort + monsterNortonCodeTwentyTwoInverseTensor := by
  rw [monsterNortonCodeTwentyTwoInversePacket, Fintype.sum_sum_type]
  change monsterNortonCodeTwentyTwoInverseShort +
    (∑ p : Fin 16 × Fin 4, ((monsterNortonCodeTwentyTwoInverseTensorCoefficient p : ℝ) /
      (32 * Real.sqrt 2)) • monsterNortonTensorUnit
        (monsterNortonCodeTwentyTwoInverseTensorIndex p).1
        (monsterNortonCodeTwentyTwoInverseTensorIndex p).2) = _
  congr 1
  unfold monsterNortonCodeTwentyTwoInverseTensor monsterNortonCodeTwentyTwoInverseSpinInteger
  simp_rw [monsterNortonUIntegerEmbed_packet]
  simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul,
    Finset.smul_sum, smul_smul, monsterNortonCodeTwentyTwoInverseTensorCoefficient,
    monsterNortonCodeTwentyTwoInverseTensorIndex, monsterNortonTensorUnit_product]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
