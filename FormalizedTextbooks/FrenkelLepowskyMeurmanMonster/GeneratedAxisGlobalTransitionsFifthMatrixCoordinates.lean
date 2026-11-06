/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Exact rational coordinate matrices for every actual fifth root-word matrix constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original physical coordinate matrix equals the real cast of the rational source word. -/
theorem generatedAxisGlobalFifthSpatialWordMatrix_coordinate (k : Fin 14) :
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord k) =
      (generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ) := by
  ext i j
  have h := congrFun (generatedAxisGlobalFifthSpatialWordMatrix_actual k (Pi.single j 1)) i
  simpa only [leechIsomMatrix, Matrix.mulVec_single_one, Matrix.col_apply] using h.symm

/-- The actual real cast of each full rational source word is orthogonal. -/
theorem generatedAxisGlobalFifthSpatialWordMatrix_orthogonal (k : Fin 14) :
    ((generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ)).transpose *
      (generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ) = 1 := by
  rw [← generatedAxisGlobalFifthSpatialWordMatrix_coordinate]
  exact leechIsomMatrix_transpose_mul _

/-- Rational source matrices determine the entire original physical matrix action. -/
theorem generatedAxisGlobalFifthSpatialWordMatrix_conjugate (k : Fin 14)
    (A : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord k) A =
      (generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ) * A *
        ((generatedAxisGlobalFifthSpatialWordMatrix k).map (Rat.castHom ℝ)).transpose := by
  rw [conwayMatrixAction_eq_conjugate, generatedAxisGlobalFifthSpatialWordMatrix_coordinate]

/-- The exact rational matrix constituent of one original normalized fifth-axis packet. -/
def generatedAxisGlobalFifthRootMatrixQ (k : Fin 14) : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalFifthSpatialWordMatrix k *
    Matrix.diagonal (fun i => if Nat.testBit 0x0f000f i.val then 1 / 2 else 1 / 4) *
      (generatedAxisGlobalFifthSpatialWordMatrix k).transpose

/-- Every entry of the real packet's matrix is exactly its rational source coordinate. -/
theorem generatedAxisGlobalFifthRootMatrixQ_actual (k : Fin 14) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)).1 =
        (generatedAxisGlobalFifthRootMatrixQ k).map (Rat.castHom ℝ) := by
  rw [generatedAxisGlobalFifthShortWord_matrix,
    generatedAxisGlobalFifthSpatialWordMatrix_conjugate, generatedAxisGlobalFifthRootMatrixQ,
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hb : Nat.testBit 0x0f000f i.val = true <;>
      norm_num [generatedAxisGlobalFifthMatrixDiagonal, Matrix.diagonal_apply,
        Matrix.map_apply, hb]
  · simp [Matrix.map_apply, hij]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
