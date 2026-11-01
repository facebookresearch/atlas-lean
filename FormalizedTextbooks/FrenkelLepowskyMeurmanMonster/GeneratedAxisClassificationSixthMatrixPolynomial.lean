/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! Polynomial recovery of a rooted two-dimensional projection from the sixth watermark. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The matrix watermark of a two-plane and its incident norm-four short line. -/
def generatedSixthRootedPlaneMatrix (P U : Matrix (Fin 24) (Fin 24) ℝ) :=
  (9 / 32 : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
    (9 / 8 : ℝ) • P - (1 / 4 : ℝ) • U

/-- A centered polynomial recovers the plane without assumed spectral information. -/
theorem generatedSixthRootedPlaneMatrix_polynomial
    (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hU : U * U = (4 : ℝ) • U)
    (hPU : P * U = U) (hUP : U * P = U) :
    let B := (32 : ℝ) • generatedSixthRootedPlaneMatrix P U - (9 : ℝ) • 1
    B * B - (40 : ℝ) • B = (-144 : ℝ) • P := by
  dsimp only
  have hB : (32 : ℝ) • generatedSixthRootedPlaneMatrix P U - (9 : ℝ) • 1 =
      (36 : ℝ) • P - (8 : ℝ) • U := by
    unfold generatedSixthRootedPlaneMatrix
    module
  rw [hB]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    hP, hU, hPU, hUP]
  module

/-- Fixing the watermark is equivalent to fixing its plane projection and short-line outer. -/
theorem generatedSixthRootedPlaneMatrix_fix_iff (g : leechIsomSubgroup)
    (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hU : U * U = (4 : ℝ) • U)
    (hPU : P * U = U) (hUP : U * P = U) :
    conwayMatrixAction g (generatedSixthRootedPlaneMatrix P U) =
        generatedSixthRootedPlaneMatrix P U ↔
      conwayMatrixAction g P = P ∧ conwayMatrixAction g U = U := by
  let B := (32 : ℝ) • generatedSixthRootedPlaneMatrix P U - (9 : ℝ) • 1
  have hpoly : B * B - (40 : ℝ) • B = (-144 : ℝ) • P :=
    generatedSixthRootedPlaneMatrix_polynomial P U hP hU hPU hUP
  have hUrecover : (36 : ℝ) • P - B = (8 : ℝ) • U := by
    dsimp [B, generatedSixthRootedPlaneMatrix]
    module
  constructor
  · intro hA
    have hB : conwayMatrixAction g B = B := by
      simp only [B, map_sub, map_smul, conwayMatrixAction_one, hA]
    have hp : (-144 : ℝ) • conwayMatrixAction g P = (-144 : ℝ) • P := by
      calc
        (-144 : ℝ) • conwayMatrixAction g P =
            conwayMatrixAction g ((-144 : ℝ) • P) := (map_smul _ _ _).symm
        _ = conwayMatrixAction g (B * B - (40 : ℝ) • B) := congrArg _ hpoly.symm
        _ = B * B - (40 : ℝ) • B := by
          rw [map_sub, map_smul, conwayMatrixAction_mul, hB]
        _ = (-144 : ℝ) • P := hpoly
    have hpfix : conwayMatrixAction g P = P :=
      (smul_right_injective _ (by norm_num : (-144 : ℝ) ≠ 0)) hp
    have hu : (8 : ℝ) • conwayMatrixAction g U = (8 : ℝ) • U := by
      calc
        (8 : ℝ) • conwayMatrixAction g U = conwayMatrixAction g ((8 : ℝ) • U) :=
          (map_smul _ _ _).symm
        _ = conwayMatrixAction g ((36 : ℝ) • P - B) := congrArg _ hUrecover.symm
        _ = (36 : ℝ) • P - B := by rw [map_sub, map_smul, hB, hpfix]
        _ = (8 : ℝ) • U := hUrecover
    exact ⟨hpfix, (smul_right_injective _ (by norm_num : (8 : ℝ) ≠ 0)) hu⟩
  · rintro ⟨hp, hu⟩
    simp only [generatedSixthRootedPlaneMatrix, map_add, map_sub, map_smul,
      conwayMatrixAction_one, hp, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
