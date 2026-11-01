/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerData

/-! The three entire original section words fix the actual whole Twelfth matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical coordinate matrix preserves multiplication of genuine lattice isometries. -/
theorem generatedTwelfth_matrix_fixer_matrix_mul (e f : leechIsomSubgroup) :
    leechIsomMatrix (e * f) = leechIsomMatrix e * leechIsomMatrix f := by
  ext j k
  change e.val (f.val (Pi.single k 1)) j = _
  rw [← leechIsomMatrix_mulVec f, ← leechIsomMatrix_mulVec e,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

/-- The original denominator-two integer frame, over the actual real coordinates. -/
def generatedTwelfthMatrixFixerHalf (M : Matrix (Fin 8) (Fin 8) ℤ) :
    Matrix (Fin 8) (Fin 8) ℝ := (1 / 2 : ℝ) • M.map (Int.castRingHom ℝ)

/-- Whole integer frame multiplication gives exactly the corresponding physical real frame. -/
theorem generatedTwelfth_matrix_fixer_half_mul (A B C : Matrix (Fin 8) (Fin 8) ℤ)
    (h : A * B = (2 : ℕ) • C) :
    generatedTwelfthMatrixFixerHalf A * generatedTwelfthMatrixFixerHalf B =
      generatedTwelfthMatrixFixerHalf C := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix h
  simp only [map_mul, map_nsmul] at hr
  change A.map (Int.castRingHom ℝ) * B.map (Int.castRingHom ℝ) =
    (2 : ℕ) • C.map (Int.castRingHom ℝ) at hr
  unfold generatedTwelfthMatrixFixerHalf
  rw [smul_mul_assoc, mul_smul_comm, hr, smul_smul]
  ext i j
  change ((1 / 2 : ℝ) * (1 / 2)) * ((2 : ℕ) • (C i j : ℝ)) = (1 / 2) * (C i j : ℝ)
  norm_num [nsmul_eq_mul]
  ring

/-- All true original physical section frames are orthogonal. -/
theorem generatedTwelfth_matrix_fixer_half_orthogonal (g : Fin 18) :
    generatedTwelfthMatrixFixerHalf (generatedTwelfthSectionGeneratorTwice g) *
      (generatedTwelfthMatrixFixerHalf (generatedTwelfthSectionGeneratorTwice g)).transpose =
      1 := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix
    (generatedTwelfth_matrix_fixer_letter_orthogonal g)
  simp only [map_mul, map_nsmul, map_one] at hr
  change (generatedTwelfthSectionGeneratorTwice g).map (Int.castRingHom ℝ) *
      (generatedTwelfthSectionGeneratorTwice g).transpose.map (Int.castRingHom ℝ) =
    (4 : ℕ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) at hr
  rw [Matrix.transpose_map] at hr
  unfold generatedTwelfthMatrixFixerHalf
  rw [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hr, smul_smul]
  ext i j
  change ((1 / 2 : ℝ) * (1 / 2)) * ((4 : ℕ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) i j) = _
  norm_num [nsmul_eq_mul]
  ring

/-- Every original letter and its genuine inverse intertwine the entire physical insertion. -/
theorem generatedTwelfth_matrix_fixer_letter_insertion (l : Fin 18 × Bool) :
    leechIsomMatrix (generatedTwelfthRootOrbitLetter l).val *
        generatedTwelfthSectionInsertionMatrix =
      generatedTwelfthSectionInsertionMatrix *
        generatedTwelfthMatrixFixerHalf (generatedTwelfthMatrixFixerLetterTwice l) := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedTwelfthSectionGenerator_insertion g
  · simp only [generatedTwelfthRootOrbitLetter, ite_true,
      generatedTwelfthMatrixFixerLetterTwice]
    simp only [Subgroup.coe_inv, generatedAxisE8FrameSystemOrbitLetter]
    have hinv : leechIsomMatrix ((generatedFifthSectionGenerator g)⁻¹) =
        (leechIsomMatrix (generatedFifthSectionGenerator g)).transpose := by
      ext j k
      exact leechIsom_inverse_coordinate _ k j
    have h := generatedTwelfthSectionGenerator_insertion g
    change leechIsomMatrix (generatedFifthSectionGenerator g) *
      generatedTwelfthSectionInsertionMatrix = generatedTwelfthSectionInsertionMatrix *
        generatedTwelfthMatrixFixerHalf (generatedTwelfthSectionGeneratorTwice g) at h
    have hc := congrArg (fun M =>
      (leechIsomMatrix (generatedFifthSectionGenerator g)).transpose * M *
        (generatedTwelfthMatrixFixerHalf (generatedTwelfthSectionGeneratorTwice g)).transpose) h
    rw [← Matrix.mul_assoc, leechIsomMatrix_transpose_mul, Matrix.one_mul] at hc
    rw [Matrix.mul_assoc, Matrix.mul_assoc, generatedTwelfth_matrix_fixer_half_orthogonal,
      Matrix.mul_one] at hc
    rw [hinv, ← hc]
    rfl

/-- Every original prefix remains a genuine full section-group element. -/
def generatedTwelfthMatrixFixerPrefixElement (g : Fin 3) (k : ℕ) :
    leechSeventhE8SectionGroup :=
  ((generatedTwelfthMatrixFixerPrefix g k).map generatedTwelfthRootOrbitLetter).prod

/-- The complete true original prefix action is the checked whole 64-entry physical frame. -/
theorem generatedTwelfth_matrix_fixer_prefix_insertion (g : Fin 3) (k : ℕ) (hk : k ≤ 13) :
    leechIsomMatrix (generatedTwelfthMatrixFixerPrefixElement g k).val *
        generatedTwelfthSectionInsertionMatrix =
      generatedTwelfthSectionInsertionMatrix *
        generatedTwelfthMatrixFixerHalf (generatedTwelfthMatrixFixerState g ⟨k, by omega⟩) := by
  induction k with
  | zero =>
    have hzero : leechIsomMatrix (1 : leechIsomSubgroup) = 1 := by
      ext i j
      simp [leechIsomMatrix, Pi.single_apply, Matrix.one_apply]
    simp only [generatedTwelfthMatrixFixerPrefixElement, generatedTwelfthMatrixFixerPrefix,
      List.map_nil, List.prod_nil, Subgroup.coe_one]
    rw [hzero, Matrix.one_mul]
    have hs : generatedTwelfthMatrixFixerState g ⟨0, by omega⟩ = (2 : ℕ) • 1 := by
      convert generatedTwelfth_matrix_fixer_state_zero g using 1
      rfl
    rw [hs]
    have hh : generatedTwelfthMatrixFixerHalf ((2 : ℕ) • (1 : Matrix (Fin 8) (Fin 8) ℤ)) = 1 := by
      unfold generatedTwelfthMatrixFixerHalf
      change (1 / 2 : ℝ) • (Int.castRingHom ℝ).mapMatrix ((2 : ℕ) • 1) = _
      rw [map_nsmul, map_one]
      ext i j
      change (1 / 2 : ℝ) * ((2 : ℕ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) i j) = _
      norm_num [nsmul_eq_mul]
      ring
    rw [hh, Matrix.mul_one]
  | succ k ih =>
    have hlt : k < 13 := by omega
    have hi := ih (by omega)
    rw [generatedTwelfthMatrixFixerPrefixElement, generatedTwelfthMatrixFixerPrefix]
    simp only [hlt, ↓reduceDIte, List.map_cons, List.prod_cons]
    simp only [Subgroup.coe_mul]
    unfold generatedTwelfthMatrixFixerPrefixElement at hi
    rw [generatedTwelfth_matrix_fixer_matrix_mul, Matrix.mul_assoc, hi,
      ← Matrix.mul_assoc, generatedTwelfth_matrix_fixer_letter_insertion, Matrix.mul_assoc]
    congr 1
    have hs := generatedTwelfth_matrix_fixer_half_mul _ _ _
      (generatedTwelfth_matrix_fixer_state_step g ⟨k, hlt⟩)
    convert hs using 1
    rfl

/-- Each displayed full original source word is an actual section isometry. -/
def generatedTwelfthMatrixFixer (g : Fin 3) : leechSeventhE8SectionGroup :=
  ((generatedTwelfthMatrixFixerWord g).map generatedTwelfthRootOrbitLetter).prod

/-- The entire original word has precisely the certified final physical coordinate frame. -/
theorem generatedTwelfth_matrix_fixer_insertion (g : Fin 3) :
    leechIsomMatrix (generatedTwelfthMatrixFixer g).val *
        generatedTwelfthSectionInsertionMatrix =
      generatedTwelfthSectionInsertionMatrix *
        generatedTwelfthMatrixFixerHalf (generatedTwelfthMatrixFixerState g 13) := by
  have h := generatedTwelfth_matrix_fixer_prefix_insertion g 13 (by omega)
  rw [generatedTwelfthMatrixFixerPrefixElement, generatedTwelfth_matrix_fixer_prefix_word] at h
  convert h using 1 <;> rfl

/-- The entire real final frame fixes the complete original golden-matrix base. -/
theorem generatedTwelfth_matrix_fixer_real_congruence (g : Fin 3) :
    generatedTwelfthMatrixFixerHalf (generatedTwelfthMatrixFixerState g 13) *
        (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) *
        (generatedTwelfthMatrixFixerHalf (generatedTwelfthMatrixFixerState g 13)).transpose =
      (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) := by
  have hr := congrArg (Int.castRingHom ℝ).mapMatrix
    (generatedTwelfth_matrix_fixer_state_congruence g)
  simp only [map_mul, map_nsmul] at hr
  change (generatedTwelfthMatrixFixerState g 13).map (Int.castRingHom ℝ) *
      (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) *
      (generatedTwelfthMatrixFixerState g 13).transpose.map (Int.castRingHom ℝ) =
    (4 : ℕ) • (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) at hr
  rw [Matrix.transpose_map] at hr
  unfold generatedTwelfthMatrixFixerHalf
  rw [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hr, smul_smul]
  ext i j
  change ((1 / 2 : ℝ) * (1 / 2)) *
    ((4 : ℕ) • (generatedTwelfthGoldenMatrixState 18197 i j : ℝ)) = _
  norm_num [nsmul_eq_mul]
  ring

/-- Each whole original source word fixes the entire actual Twelfth axis matrix. -/
theorem generatedTwelfth_matrix_fixer_actual_matrix (g : Fin 3) :
    conwayMatrixAction (generatedTwelfthMatrixFixer g).val
        (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1 := by
  rw [← generatedTwelfthGoldenOrbit_axis_base]
  unfold generatedTwelfthGoldenOrbitAxisMatrix
  rw [map_smul, map_add, map_nsmul, conwayMatrixAction_one]
  congr 2
  rw [conwayMatrixAction_eq_conjugate]
  unfold generatedTwelfthSectionMatrix
  have he : leechIsomMatrix (generatedTwelfthMatrixFixer g).val *
      (generatedTwelfthSectionInsertionMatrix *
        (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) *
        generatedTwelfthSectionInsertionMatrix.transpose) *
      (leechIsomMatrix (generatedTwelfthMatrixFixer g).val).transpose =
    (leechIsomMatrix (generatedTwelfthMatrixFixer g).val *
      generatedTwelfthSectionInsertionMatrix) *
      (generatedTwelfthGoldenMatrixState 18197).map (Int.castRingHom ℝ) *
      (leechIsomMatrix (generatedTwelfthMatrixFixer g).val *
        generatedTwelfthSectionInsertionMatrix).transpose := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [he, generatedTwelfth_matrix_fixer_insertion, Matrix.transpose_mul]
  have hc := congrArg (fun M => generatedTwelfthSectionInsertionMatrix * M *
      generatedTwelfthSectionInsertionMatrix.transpose)
    (generatedTwelfth_matrix_fixer_real_congruence g)
  simpa only [Matrix.mul_assoc] using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
