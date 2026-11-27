/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsIntDecomposableFormEvalEqDetPowMulPow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import MathlibExt.NumberTheory.Recurrences.BinaryRecurrenceQuadraticForm
import MathlibExt.NumberTheory.Recurrences.HomogeneousFormLinearRecurrence

/-! # Tests for integer decomposable forms on integer recurrence sequences -/

namespace MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsIntDecomposableFormEvalEqDetPowMulPow

-- Fibonacci and Lucas initial data give determinant `-2`, so the form takes the
-- values `4` and `-4` at times `0` and `1`.
example : ∃ F : MvPolynomial (Fin 2) ℤ,
    (∃ L : Fin 2 → MvPolynomial (Fin 2) ℂ, (∀ i, (L i).IsHomogeneous 1) ∧
      MvPolynomial.map (Int.castRingHom ℂ) F = ∏ i, L i) ∧
    MvPolynomial.eval ![0, 2] F = 4 ∧ MvPolynomial.eval ![1, 1] F = -4 := by
  let E : LinearRecurrence ℤ := ⟨2, ![1, 1]⟩
  let G : Fin 2 → ℕ → ℤ := ![E.mkSol ![0, 1], E.mkSol ![2, 1]]
  have hG : ∀ j, E.IsSolution (G j) := by
    intro j
    fin_cases j
    · simpa [G] using E.is_sol_mkSol ![0, 1]
    · simpa [G] using E.is_sol_mkSol ![2, 1]
  have hc : E.charPoly.coeff 0 = -1 := by
    change (Polynomial.monomial 2 (1 : ℤ) -
      ∑ i : Fin 2, Polynomial.monomial i (![(1 : ℤ), 1] i)).coeff 0 = -1
    rw [Fin.sum_univ_two]
    norm_num [Polynomial.coeff_monomial]
  have hγ : E.charPoly.coeff 0 ≠ 0 := by rw [hc]; norm_num
  have e00 : G 0 0 = 0 := by
    have h := E.mkSol_eq_init ![0, 1] (0 : Fin 2)
    simpa [G] using h
  have e01 : G 0 1 = 1 := by
    have h := E.mkSol_eq_init ![0, 1] (1 : Fin 2)
    simpa [G, E] using h
  have e10 : G 1 0 = 2 := by
    have h := E.mkSol_eq_init ![2, 1] (0 : Fin 2)
    simpa [G] using h
  have e11 : G 1 1 = 1 := by
    have h := E.mkSol_eq_init ![2, 1] (1 : Fin 2)
    simpa [G, E] using h
  have hdet : (Matrix.of fun j i : Fin 2 => G j i).det = -2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    change G 0 0 * G 1 1 - G 0 1 * G 1 0 = -2
    rw [e00, e01, e10, e11]
    norm_num
  have hΔ : (Matrix.of fun j i : Fin 2 => G j i).det ≠ 0 := by rw [hdet]; norm_num
  obtain ⟨F, hdecomp, heval⟩ :=
    MetaMathlibExt.exists_int_decomposable_form_eval_eq_det_pow_mul_pow E G hG hγ hΔ
  have hvalue0 : (fun j => G j 0) = ![0, 2] := by
    funext j
    fin_cases j
    · exact e00
    · exact e10
  have hvalue1 : (fun j => G j 1) = ![1, 1] := by
    funext j
    fin_cases j
    · exact e01
    · exact e11
  refine ⟨F, hdecomp, ?_, ?_⟩
  · have h0 := heval 0
    rw [hvalue0, hdet, hc] at h0
    norm_num at h0
    exact h0
  · have h1 := heval 1
    rw [hvalue1, hdet, hc] at h1
    norm_num at h1
    exact h1

-- The geometric sequence `3 * 2 ^ n` has initial determinant `3`, so the linear form
-- takes the values `3` and `6` at times `0` and `1`.
example : ∃ F : MvPolynomial (Fin 1) ℤ,
    (∃ L : Fin 1 → MvPolynomial (Fin 1) ℂ, (∀ i, (L i).IsHomogeneous 1) ∧
      MvPolynomial.map (Int.castRingHom ℂ) F = ∏ i, L i) ∧
    MvPolynomial.eval ![3] F = 3 ∧ MvPolynomial.eval ![6] F = 6 := by
  let E : LinearRecurrence ℤ := ⟨1, ![2]⟩
  let G : Fin 1 → ℕ → ℤ := ![fun n => 3 * 2 ^ n]
  have hG : ∀ j, E.IsSolution (G j) := by
    intro j
    fin_cases j
    intro n
    change (3 : ℤ) * 2 ^ (n + 1) = ∑ i : Fin 1, ![2] i * (3 * 2 ^ (n + (i : ℕ)))
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    change (3 : ℤ) * 2 ^ (n + 1) = 2 * (3 * 2 ^ n)
    ring
  have hc : E.charPoly.coeff 0 = -2 := by
    change (Polynomial.monomial 1 (1 : ℤ) -
      ∑ i : Fin 1, Polynomial.monomial i (![(2 : ℤ)] i)).coeff 0 = -2
    rw [Fin.sum_univ_one]
    norm_num [Polynomial.coeff_monomial]
  have hγ : E.charPoly.coeff 0 ≠ 0 := by rw [hc]; norm_num
  have hdet : (Matrix.of fun j i : Fin 1 => G j i).det = 3 := by
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply]
    simp [G]
  have hΔ : (Matrix.of fun j i : Fin 1 => G j i).det ≠ 0 := by rw [hdet]; norm_num
  obtain ⟨F, hdecomp, heval⟩ :=
    MetaMathlibExt.exists_int_decomposable_form_eval_eq_det_pow_mul_pow E G hG hγ hΔ
  have hvalue0 : (fun j => G j 0) = ![3] := by
    funext j
    fin_cases j
    simp [G]
  have hvalue1 : (fun j => G j 1) = ![6] := by
    funext j
    fin_cases j
    simp only [G]
    norm_num
  refine ⟨F, hdecomp, ?_, ?_⟩
  · have h0 := heval 0
    rw [hvalue0, hdet, hc] at h0
    norm_num at h0
    exact h0
  · have h1 := heval 1
    rw [hvalue1, hdet, hc] at h1
    norm_num at h1
    exact h1

end MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsIntDecomposableFormEvalEqDetPowMulPow
