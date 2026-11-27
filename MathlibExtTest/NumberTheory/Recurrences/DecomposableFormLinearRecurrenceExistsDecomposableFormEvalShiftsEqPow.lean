/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceExistsDecomposableFormEvalShiftsEqPow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for decomposable forms on consecutive recurrence terms

The example covers a repeated characteristic root at every integer index.
-/

namespace MathlibExtTest.NumberTheory.Recurrences
namespace DecomposableFormLinearRecurrenceExistsDecomposableFormEvalShiftsEqPow

example : ∃ L : Fin 2 → MvPolynomial (Fin 2) ℂ, (∀ i, (L i).IsHomogeneous 1) ∧
    ∀ n : ℤ, MvPolynomial.eval
      (fun j : Fin 2 ↦ ((n + (j : ℕ) : ℤ) : ℂ) * 2 ^ (n + (j : ℕ)))
      (∏ i, L i) = (4 : ℂ) ^ n := by
  let E : LinearRecurrence ℂ := ⟨2, ![-4, 4]⟩
  let G (n : ℤ) : ℂ := (n : ℂ) * 2 ^ n
  have hG (n : ℤ) :
      G (n + E.order) = ∑ i, E.coeffs i * G (n + (i : ℕ)) := by
    change G (n + 2) = ∑ i : Fin 2, ![(-4 : ℂ), 4] i * G (n + (i : ℕ))
    rw [Fin.sum_univ_two]
    norm_num [G, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
    ring
  have hi : LinearIndependent ℂ fun j : Fin 2 => fun i : Fin 2 =>
      G ((j : ℕ) + (i : ℕ)) := by
    apply linearIndependent_fin2.2
    constructor
    · intro h
      have := congrFun h 1
      norm_num [G] at this
    · intro a h
      have := congrFun h 0
      norm_num [G] at this
      have h1 := congrFun h 1
      norm_num [G, this] at h1
  obtain ⟨L, hL, heval⟩ :=
    MetaMathlibExt.exists_decomposable_form_eval_shifts_eq_pow E G hG hi
  have hc : E.charPoly.coeff 0 = 4 := by
    change (Polynomial.monomial 2 1 -
      ∑ i : Fin 2, Polynomial.monomial i (![(-4 : ℂ), 4] i)).coeff 0 = 4
    rw [Fin.sum_univ_two]
    norm_num [Polynomial.coeff_monomial]
  refine ⟨L, hL, fun n ↦ ?_⟩
  simpa [E, G, hc] using heval n

end DecomposableFormLinearRecurrenceExistsDecomposableFormEvalShiftsEqPow
end MathlibExtTest.NumberTheory.Recurrences
