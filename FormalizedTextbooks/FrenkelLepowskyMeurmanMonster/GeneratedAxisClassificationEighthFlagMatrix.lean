/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! Recover the two orthogonal projections from the eighth coordinate matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual matrix expression for a coordinate subspace and an orthogonal line. -/
def generatedEighthCoordinateFlagMatrix (P L : Matrix (Fin 24) (Fin 24) ℝ) :=
  (1 / 4 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
    (1 / 8 : ℝ) • P + (1 / 2 : ℝ) • L

/-- A polynomial recovers the line without a spectral assumption. -/
theorem generatedEighthCoordinateFlagMatrix_polynomial
    (P L : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hL : L * L = L) (hPL : P * L = 0) (hLP : L * P = 0) :
    let B := (8 : ℝ) • generatedEighthCoordinateFlagMatrix P L - (2 : ℝ) • 1
    B * B - B = (12 : ℝ) • L := by
  dsimp only
  have hB : (8 : ℝ) • generatedEighthCoordinateFlagMatrix P L - (2 : ℝ) • 1 =
      P + (4 : ℝ) • L := by
    unfold generatedEighthCoordinateFlagMatrix
    module
  rw [hB]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hP, hL, hPL, hLP, smul_zero, add_zero, zero_add]
  module

/-- Fixing this matrix fixes both its genuine orthogonal projections. -/
theorem generatedEighthCoordinateFlagMatrix_fix_iff (g : leechIsomSubgroup)
    (P L : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hL : L * L = L) (hPL : P * L = 0) (hLP : L * P = 0) :
    conwayMatrixAction g (generatedEighthCoordinateFlagMatrix P L) =
        generatedEighthCoordinateFlagMatrix P L ↔
      conwayMatrixAction g P = P ∧ conwayMatrixAction g L = L := by
  let B := (8 : ℝ) • generatedEighthCoordinateFlagMatrix P L - (2 : ℝ) • 1
  have hpoly : B * B - B = (12 : ℝ) • L :=
    generatedEighthCoordinateFlagMatrix_polynomial P L hP hL hPL hLP
  have hPrecover : B - (4 : ℝ) • L = P := by
    dsimp [B, generatedEighthCoordinateFlagMatrix]
    module
  constructor
  · intro hA
    have hB : conwayMatrixAction g B = B := by
      simp only [B, map_sub, map_smul, conwayMatrixAction_one, hA]
    have hl : (12 : ℝ) • conwayMatrixAction g L = (12 : ℝ) • L := by
      calc
        (12 : ℝ) • conwayMatrixAction g L = conwayMatrixAction g ((12 : ℝ) • L) :=
          (map_smul _ _ _).symm
        _ = conwayMatrixAction g (B * B - B) := congrArg _ hpoly.symm
        _ = B * B - B := by rw [map_sub, conwayMatrixAction_mul, hB]
        _ = (12 : ℝ) • L := hpoly
    have hlfix : conwayMatrixAction g L = L :=
      (smul_right_injective _ (by norm_num : (12 : ℝ) ≠ 0)) hl
    have hpfix : conwayMatrixAction g P = P := by
      calc
        conwayMatrixAction g P = conwayMatrixAction g (B - (4 : ℝ) • L) :=
          congrArg _ hPrecover.symm
        _ = B - (4 : ℝ) • L := by rw [map_sub, map_smul, hB, hlfix]
        _ = P := hPrecover
    exact ⟨hpfix, hlfix⟩
  · rintro ⟨hp, hl⟩
    simp only [generatedEighthCoordinateFlagMatrix, map_add, map_smul,
      conwayMatrixAction_one, hp, hl]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
