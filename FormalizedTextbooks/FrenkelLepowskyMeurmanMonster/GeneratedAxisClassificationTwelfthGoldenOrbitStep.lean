/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionMatrices

/-! Every finite integer matrix edge becomes a genuine ambient original-generator orbit step. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An exact integer conjugation equation gives the full genuine original ambient matrix action. -/
theorem generatedTwelfthGoldenOrbit_integer_step (g : Fin 18)
    (M N : Matrix (Fin 8) (Fin 8) ℤ)
    (h : generatedTwelfthSectionGeneratorTwice g * M *
      (generatedTwelfthSectionGeneratorTwice g).transpose = (4 : ℕ) • N) :
    conwayMatrixAction (generatedFifthSectionGenerator g)
      (generatedTwelfthSectionMatrix (M.map (Int.castRingHom ℝ))) =
        generatedTwelfthSectionMatrix (N.map (Int.castRingHom ℝ)) := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix h
  simp only [map_mul, map_nsmul] at hr
  change (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ) *
    M.map (Int.castRingHom ℝ) *
    ((generatedTwelfthSectionGeneratorTwice g).transpose.map (Int.castRingHom ℝ)) =
      (4 : ℕ) • N.map (Int.castRingHom ℝ) at hr
  rw [Matrix.transpose_map] at hr
  rw [generatedTwelfthSectionGenerator_matrix_action, Matrix.transpose_smul,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hr, smul_smul]
  congr 1
  ext i j
  change ((1 / 2 : ℝ) * (1 / 2)) * ((4 : ℕ) • (N i j : ℝ)) = (N i j : ℝ)
  norm_num [nsmul_eq_mul]
  ring

/-- The original monomial matrices have their exact signed-coordinate conjugation action. -/
theorem generatedTwelfthGoldenOrbit_monomial_integer (g : Fin 17)
    (M : Matrix (Fin 8) (Fin 8) ℤ) (i j : Fin 8) :
    (generatedTwelfthSectionGeneratorTwice (Fin.castLE (by decide : 17 ≤ 18) g) * M *
      (generatedTwelfthSectionGeneratorTwice (Fin.castLE (by decide : 17 ≤ 18) g)).transpose) i j =
      4 * generatedTwelfthGoldenMonomialSign g i * generatedTwelfthGoldenMonomialSign g j *
        M (generatedTwelfthGoldenMonomialCoordinate g i)
          (generatedTwelfthGoldenMonomialCoordinate g j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [generatedTwelfthGoldenMonomial_source]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check the sole original Xi edge, including every physical-coordinate integer matrix entry.
/-- The unique nonmonomial anchor is an exact original Xi conjugation equation. -/
theorem generatedTwelfthGoldenOrbit_xi_anchor :
    generatedTwelfthSectionGeneratorTwice 17 * generatedTwelfthGoldenMatrixState 18203 *
      (generatedTwelfthSectionGeneratorTwice 17).transpose =
        (4 : ℕ) • generatedTwelfthGoldenMatrixState 22875 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
