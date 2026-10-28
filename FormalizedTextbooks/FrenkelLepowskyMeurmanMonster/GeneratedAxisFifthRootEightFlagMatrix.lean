/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! Recover the two distinguished projections from the root-8 matrix polynomial. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The source matrix associated with two orthogonal distinguished lines. -/
def generatedFifthRootEightCoordinateFlagMatrix (P L : Matrix (Fin 24) (Fin 24) ℝ) :=
  (5 / 16 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
    (5 / 8 : ℝ) • P - (1 / 8 : ℝ) • L

/-- A polynomial recovers the higher-line projection without a spectral assumption. -/
theorem generatedFifthRootEightCoordinateFlagMatrix_polynomial
    (P L : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hL : L * L = L) (hPL : P * L = 0) (hLP : L * P = 0) :
    let B := (16 : ℝ) • generatedFifthRootEightCoordinateFlagMatrix P L - (5 : ℝ) • 1
    B * B + (2 : ℝ) • B = (120 : ℝ) • P := by
  dsimp only
  have hB : (16 : ℝ) • generatedFifthRootEightCoordinateFlagMatrix P L - (5 : ℝ) • 1 =
      (10 : ℝ) • P - (2 : ℝ) • L := by
    unfold generatedFifthRootEightCoordinateFlagMatrix
    module
  rw [hB]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    hP, hL, hPL, hLP, smul_zero, sub_zero, zero_sub]
  module

/-- Fixing this matrix is equivalent to fixing both distinguished line projections. -/
theorem generatedFifthRootEightCoordinateFlagMatrix_fix_iff (g : leechIsomSubgroup)
    (P L : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hL : L * L = L) (hPL : P * L = 0) (hLP : L * P = 0) :
    conwayMatrixAction g (generatedFifthRootEightCoordinateFlagMatrix P L) =
        generatedFifthRootEightCoordinateFlagMatrix P L ↔
      conwayMatrixAction g P = P ∧ conwayMatrixAction g L = L := by
  let B := (16 : ℝ) • generatedFifthRootEightCoordinateFlagMatrix P L - (5 : ℝ) • 1
  have hpoly : B * B + (2 : ℝ) • B = (120 : ℝ) • P :=
    generatedFifthRootEightCoordinateFlagMatrix_polynomial P L hP hL hPL hLP
  have hrecover : (10 : ℝ) • P - B = (2 : ℝ) • L := by
    dsimp [B, generatedFifthRootEightCoordinateFlagMatrix]
    module
  constructor
  · intro hA
    have hB : conwayMatrixAction g B = B := by
      simp only [B, map_sub, map_smul, conwayMatrixAction_one, hA]
    have hp : (120 : ℝ) • conwayMatrixAction g P = (120 : ℝ) • P := by
      calc
        (120 : ℝ) • conwayMatrixAction g P =
            conwayMatrixAction g ((120 : ℝ) • P) := (map_smul _ _ _).symm
        _ = conwayMatrixAction g (B * B + (2 : ℝ) • B) := congrArg _ hpoly.symm
        _ = B * B + (2 : ℝ) • B := by
          rw [map_add, map_smul, conwayMatrixAction_mul, hB]
        _ = (120 : ℝ) • P := hpoly
    have hpfix : conwayMatrixAction g P = P :=
      (smul_right_injective _ (by norm_num : (120 : ℝ) ≠ 0)) hp
    have hl : (2 : ℝ) • conwayMatrixAction g L = (2 : ℝ) • L := by
      calc
        (2 : ℝ) • conwayMatrixAction g L =
            conwayMatrixAction g ((2 : ℝ) • L) := (map_smul _ _ _).symm
        _ = conwayMatrixAction g ((10 : ℝ) • P - B) := congrArg _ hrecover.symm
        _ = (10 : ℝ) • P - B := by rw [map_sub, map_smul, hpfix, hB]
        _ = (2 : ℝ) • L := hrecover
    exact ⟨hpfix, (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hl⟩
  · rintro ⟨hp, hl⟩
    simp only [generatedFifthRootEightCoordinateFlagMatrix, map_sub, map_add, map_smul,
      conwayMatrixAction_one, hp, hl]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
