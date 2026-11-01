/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGeneratorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialSection

/-! The actual physical E8 matrix insertion intertwines every original section-generator action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The rectangular matrix of the original physical octad-coordinate insertion. -/
def generatedTwelfthSectionInsertionMatrix : Matrix (Fin 24) (Fin 8) ℝ :=
  LinearMap.toMatrix' generatedTwelfthSectionInsertReal

/-- Insert every full physical section matrix into the genuine ambient 24-coordinate matrix. -/
def generatedTwelfthSectionMatrix (M : Matrix (Fin 8) (Fin 8) ℝ) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  generatedTwelfthSectionInsertionMatrix * M * generatedTwelfthSectionInsertionMatrix.transpose

/-- The original coordinate matrix inserts every real section vector exactly. -/
theorem generatedTwelfthSectionInsertionMatrix_mulVec (v : Fin 8 → ℝ) :
    generatedTwelfthSectionInsertionMatrix *ᵥ v = generatedTwelfthSectionInsertReal v :=
  LinearMap.toMatrix'_mulVec _ _

/-- Every entire original generator intertwines the true physical coordinate insertion. -/
theorem generatedTwelfthSectionGenerator_insertion (g : Fin 18) :
    leechIsomMatrix (generatedFifthSectionGenerator g) * generatedTwelfthSectionInsertionMatrix =
      generatedTwelfthSectionInsertionMatrix *
        ((1 / 2 : ℝ) • (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ)) := by
  ext i j
  change (leechIsomMatrix (generatedFifthSectionGenerator g) *ᵥ
    generatedTwelfthSectionInsertionMatrix.col j) i =
    (generatedTwelfthSectionInsertionMatrix *ᵥ
      (((1 / 2 : ℝ) • (generatedTwelfthSectionGeneratorTwice g).map
        (Int.castRingHom ℝ)).col j)) i
  rw [leechIsomMatrix_mulVec]
  have hc : generatedTwelfthSectionInsertionMatrix.col j =
      generatedTwelfthSectionInsertReal (Pi.single j 1) := by
    rw [← Matrix.mulVec_single_one, generatedTwelfthSectionInsertionMatrix_mulVec]
  rw [hc, generatedTwelfthSectionInsertionMatrix_mulVec]
  have h := generatedTwelfthSectionGenerator_real_action g (Pi.single j 1)
  rw [← Matrix.smul_mulVec, Matrix.mulVec_single_one] at h
  exact congrFun h i

/-- The complete ambient actual matrix action is the checked physical E8 conjugation. -/
theorem generatedTwelfthSectionGenerator_matrix_action (g : Fin 18)
    (M : Matrix (Fin 8) (Fin 8) ℝ) :
    conwayMatrixAction (generatedFifthSectionGenerator g) (generatedTwelfthSectionMatrix M) =
      generatedTwelfthSectionMatrix
        (((1 / 2 : ℝ) • (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ)) *
          M * (((1 / 2 : ℝ) •
            (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ))).transpose) := by
  rw [conwayMatrixAction_eq_conjugate]
  unfold generatedTwelfthSectionMatrix
  calc
    _ = (leechIsomMatrix (generatedFifthSectionGenerator g) *
          generatedTwelfthSectionInsertionMatrix) * M *
        (leechIsomMatrix (generatedFifthSectionGenerator g) *
          generatedTwelfthSectionInsertionMatrix).transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [generatedTwelfthSectionGenerator_insertion, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
