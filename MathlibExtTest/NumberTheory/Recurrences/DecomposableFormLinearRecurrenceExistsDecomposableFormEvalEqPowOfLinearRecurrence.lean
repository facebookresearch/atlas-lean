/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsDecomposableFormEvalEqPowOfLinearRecurrence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for decomposable forms on bilateral recurrences -/

namespace MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsDecomposableFormEvalEqPowOfLinearRecurrence

-- The empty family has characteristic polynomial 1 and gives an empty product of forms.
example : ∃ L : Fin 0 → MvPolynomial (Fin 0) ℂ, (∀ i, (L i).IsHomogeneous 1) ∧
    MvPolynomial.eval Fin.elim0 (∏ i, L i) = 1 := by
  let E : LinearRecurrence ℂ := ⟨0, Fin.elim0⟩
  obtain ⟨L, hL, heval⟩ := MetaMathlibExt.exists_decomposable_form_eval_eq_pow_of_linearRecurrence
    E (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) linearIndependent_empty_type
  refine ⟨L, hL, ?_⟩
  have hv : (fun j : Fin 0 ↦ (Fin.elim0 j : ℤ → ℂ) 0) = Fin.elim0 := Subsingleton.elim _ _
  rw [← hv]
  exact (heval 0).trans (zpow_zero _)

-- The double root 2 gives solutions 2^n and n * 2^n. At time -1 the decomposable form
-- must take the reciprocal of 4 on their values.
example : ∃ L : Fin 2 → MvPolynomial (Fin 2) ℂ, (∀ i, (L i).IsHomogeneous 1) ∧
    MvPolynomial.eval ![(1 / 2 : ℂ), -(1 / 2)] (∏ i, L i) = 1 / 4 := by
  let E : LinearRecurrence ℂ := ⟨2, ![-4, 4]⟩
  let G : Fin 2 → ℤ → ℂ := ![fun n ↦ (2 : ℂ) ^ n, fun n ↦ (n : ℂ) * 2 ^ n]
  have hr (j : Fin 2) (n : ℤ) :
      G j (n + E.order) = ∑ i, E.coeffs i * G j (n + (i : ℕ)) := by
    change G j (n + 2) = ∑ i : Fin 2, ![(-4 : ℂ), 4] i * G j (n + (i : ℕ))
    rw [Fin.sum_univ_two]
    fin_cases j <;> norm_num [G, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)] <;> ring
  have hi : LinearIndependent ℂ G := by
    apply linearIndependent_fin2.2
    constructor
    · intro h
      have := congrFun h 1
      norm_num [G] at this
    · intro a h
      have := congrFun h 0
      norm_num [G] at this
  obtain ⟨L, hL, heval⟩ := MetaMathlibExt.exists_decomposable_form_eval_eq_pow_of_linearRecurrence
    E G hr hi
  have hvalue : (fun j ↦ G j (-1)) = ![(1 / 2 : ℂ), -(1 / 2)] := by
    funext j
    fin_cases j <;> norm_num [G]
  refine ⟨L, hL, ?_⟩
  have hc : E.charPoly.coeff 0 = 4 := by
    change (Polynomial.monomial 2 1 -
      ∑ i : Fin 2, Polynomial.monomial i (![(-4 : ℂ), 4] i)).coeff 0 = 4
    rw [Fin.sum_univ_two]
    norm_num [Polynomial.coeff_monomial]
  rw [← hvalue, heval, hc]
  norm_num [E]

end MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsDecomposableFormEvalEqPowOfLinearRecurrence
