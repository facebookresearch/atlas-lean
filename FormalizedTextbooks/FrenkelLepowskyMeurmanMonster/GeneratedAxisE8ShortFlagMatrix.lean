/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import Mathlib.Tactic.Module

/-! Polynomial recovery of the E8 projection and its incident short-line matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The physical matrix of an E8 section-short-line flag. -/
def generatedAxisE8ShortFlagMatrix (P U : Matrix (Fin 24) (Fin 24) ℝ) :=
  (3 / 8 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) - (1 / 4 : ℝ) • P + (1 / 4 : ℝ) • U

/-- The section projection is recovered by a polynomial in the centered flag matrix. -/
theorem generatedAxisE8ShortFlagMatrix_polynomial
    (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hU : U * U = (4 : ℝ) • U)
    (hPU : P * U = U) (hUP : U * P = U) :
    let B := (8 : ℝ) • generatedAxisE8ShortFlagMatrix P U - (3 : ℝ) • 1
    B * B - (4 : ℝ) • B = (12 : ℝ) • P := by
  dsimp only
  have hB : (8 : ℝ) • generatedAxisE8ShortFlagMatrix P U - (3 : ℝ) • 1 =
      (-2 : ℝ) • P + (2 : ℝ) • U := by
    unfold generatedAxisE8ShortFlagMatrix
    module
  rw [hB]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hP, hU, hPU, hUP]
  module

/-- Fixing the actual flag matrix fixes both its section projection and its short line. -/
theorem generatedAxisE8ShortFlagMatrix_fix_iff (g : leechIsomSubgroup)
    (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hU : U * U = (4 : ℝ) • U)
    (hPU : P * U = U) (hUP : U * P = U) :
    conwayMatrixAction g (generatedAxisE8ShortFlagMatrix P U) =
        generatedAxisE8ShortFlagMatrix P U ↔
      conwayMatrixAction g P = P ∧ conwayMatrixAction g U = U := by
  let B := (8 : ℝ) • generatedAxisE8ShortFlagMatrix P U - (3 : ℝ) • 1
  have hpoly : B * B - (4 : ℝ) • B = (12 : ℝ) • P :=
    generatedAxisE8ShortFlagMatrix_polynomial P U hP hU hPU hUP
  have hUrecover : B + (2 : ℝ) • P = (2 : ℝ) • U := by
    dsimp [B, generatedAxisE8ShortFlagMatrix]
    module
  constructor
  · intro hA
    have hB : conwayMatrixAction g B = B := by
      simp only [B, map_sub, map_smul, conwayMatrixAction_one, hA]
    have hp : (12 : ℝ) • conwayMatrixAction g P = (12 : ℝ) • P := by
      calc
        (12 : ℝ) • conwayMatrixAction g P = conwayMatrixAction g ((12 : ℝ) • P) :=
          (map_smul _ _ _).symm
        _ = conwayMatrixAction g (B * B - (4 : ℝ) • B) := congrArg _ hpoly.symm
        _ = B * B - (4 : ℝ) • B := by
          rw [map_sub, map_smul, conwayMatrixAction_mul, hB]
        _ = (12 : ℝ) • P := hpoly
    have hpfix : conwayMatrixAction g P = P :=
      (smul_right_injective _ (by norm_num : (12 : ℝ) ≠ 0)) hp
    have hu : (2 : ℝ) • conwayMatrixAction g U = (2 : ℝ) • U := by
      calc
        (2 : ℝ) • conwayMatrixAction g U = conwayMatrixAction g ((2 : ℝ) • U) :=
          (map_smul _ _ _).symm
        _ = conwayMatrixAction g (B + (2 : ℝ) • P) := congrArg _ hUrecover.symm
        _ = B + (2 : ℝ) • P := by rw [map_add, map_smul, hB, hpfix]
        _ = (2 : ℝ) • U := hUrecover
    exact ⟨hpfix, (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) hu⟩
  · rintro ⟨hp, hu⟩
    simp only [generatedAxisE8ShortFlagMatrix, map_add, map_sub, map_smul,
      conwayMatrixAction_one, hp, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
