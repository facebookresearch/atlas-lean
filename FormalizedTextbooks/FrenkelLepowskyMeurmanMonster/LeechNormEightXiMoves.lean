/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact first-tetrad arithmetic for the actual three-bases lattice action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The real source matrix is half its displayed integer numerator. -/
theorem co1XiMatrix_half_numerator : co1XiMatrix =
    (1 / 2 : ℝ) • co1XiNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  simp [co1XiMatrix, co1XiMatrixQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- Twice the actual integral action is the exact integer numerator action. -/
theorem co1Xi_integral_double (u : leechIntegral) :
    (2 : ℕ) • (leechIntegralAction co1XiIsometry u).val = co1XiNumerator *ᵥ u.val := by
  have he := leechIntegralAction_embedding co1XiIsometry u
  change leechCoordinateEmbedding (leechIntegralAction co1XiIsometry u).val =
    co1XiMatrix *ᵥ leechCoordinateEmbedding u.val at he
  rw [co1XiMatrix_half_numerator, Matrix.smul_mulVec,
    ← leechCoordinateEmbedding_mulVec] at he
  apply leechCoordinateEmbedding_injective
  rw [map_nsmul, he]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- All four first-tetrad numerator rows are computed exactly. -/
theorem co1Xi_first_four_numerator (u : Fin 24 → ℤ) :
    (co1XiNumerator *ᵥ u) 0 = -u 0 + u 1 + u 2 + u 3 ∧
    (co1XiNumerator *ᵥ u) 1 = -u 0 + u 1 - u 2 - u 3 ∧
    (co1XiNumerator *ᵥ u) 2 = -u 0 - u 1 + u 2 - u 3 ∧
    (co1XiNumerator *ᵥ u) 3 = -u 0 - u 1 - u 2 + u 3 := by
  simp [co1XiNumerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
