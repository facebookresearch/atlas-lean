/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact normalization between integral tensor inputs and physical spin columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem first_integral_column :
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ (Pi.single 0 1 : Fin 24 → ℤ)) =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single 0 1 : Fin 24 → ℝ) := by
  have hb : leechBasisMatrix *ᵥ (Pi.single 0 1 : Fin 24 → ℤ) = Pi.single 0 8 := by
    decide +kernel
  rw [hb]
  ext i
  by_cases hi : i = 0
  · subst i
    simp [leechCoordinateEmbedding]
  · simp [leechCoordinateEmbedding, hi]

private theorem sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  calc
    Real.sqrt 8 = Real.sqrt (4 * 2) := by norm_num
    _ = Real.sqrt 4 * Real.sqrt 2 := Real.sqrt_mul (by norm_num) _
    _ = 2 * Real.sqrt 2 := by norm_num

/-- The first integral Leech column gives the exact physical tensor normalization. -/
theorem monsterNortonIntegralTensorVector_first_column (v : NortonUIntegerVector) :
    (1 / 4 : ℝ) • monsterNortonIntegralTensorVector v (Pi.single 0 1) =
      (1 / Real.sqrt 2 : ℝ) •
        monsterNortonTensorLift (conwaySpinColumn (nortonUIntegerEmbed v) 0) := by
  have hc : conwayTensorCoordinates
      (nortonUIntegerEmbed v ⊗ₜ[ℝ] (Pi.single 0 1 : Fin 24 → ℝ)) =
        conwaySpinColumn (nortonUIntegerEmbed v) 0 := by
    ext t i
    simp [conwayTensorCoordinates_tmul, conwaySpinColumn, Pi.single_apply]
  change (1 / 4 : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
    (nortonUIntegerEmbed v ⊗ₜ[ℝ]
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (Pi.single 0 1)))) = _
  rw [first_integral_column, TensorProduct.tmul_smul, map_smul, map_smul,
    smul_smul, hc]
  congr 1
  rw [sqrt_eight]
  field_simp
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
