/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceAlgebraicDependence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for algebraic dependence of bilateral recurrence sequences -/

namespace MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceAlgebraicDependence

open MetaMathlibExt

-- At even order the adjoined sequence has base -2, while the determinant has base 2.
example : ¬ AlgebraicIndependent ℂ fun o : Option (Fin 2) ↦
    o.elim (fun n : ℤ ↦ (-2 : ℂ) ^ n) (![fun _ ↦ 1, fun n : ℤ ↦ (2 : ℂ) ^ n]) := by
  let E : LinearRecurrence ℂ := ⟨2, ![-2, 3]⟩
  let G : Fin 2 → ℤ → ℂ := ![fun _ ↦ 1, fun n ↦ (2 : ℂ) ^ n]
  have hG (j : Fin 2) (n : ℤ) :
      G j (n + E.order) = ∑ i, E.coeffs i * G j (n + (i : ℕ)) := by
    change G j (n + 2) = ∑ i : Fin 2, ![(-2 : ℂ), 3] i * G j (n + (i : ℕ))
    rw [Fin.sum_univ_two]
    fin_cases j <;> norm_num [G, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]; ring
  have hcoeff : E.charPoly.coeff 0 = 2 := by
    change (Polynomial.monomial 2 1 -
      ∑ i : Fin 2, Polynomial.monomial i (![(-2 : ℂ), 3] i)).coeff 0 = 2
    rw [Fin.sum_univ_two]
    norm_num [Polynomial.coeff_monomial]
  simpa only [hcoeff] using not_algebraicIndependent_linearRecurrence_solutions_pow E G hG

-- For zero constant coefficient, the result retains Lean's integer powers of zero.
example : ¬ AlgebraicIndependent ℂ fun o : Option (Fin 1) ↦
    o.elim (fun n : ℤ ↦ (0 : ℂ) ^ n) (fun _ _ ↦ 0) := by
  let E : LinearRecurrence ℂ := ⟨1, fun _ ↦ 0⟩
  have hcoeff : E.charPoly.coeff 0 = 0 := by
    simp [E, LinearRecurrence.charPoly, Polynomial.coeff_monomial]
  simpa only [hcoeff, neg_zero] using
    not_algebraicIndependent_linearRecurrence_solutions_pow E (fun _ _ ↦ 0) (by simp)

-- Order zero leaves just the alternating power sequence.
example : ¬ AlgebraicIndependent ℂ fun o : Option (Fin 0) ↦
    o.elim (fun n : ℤ ↦ (-1 : ℂ) ^ n) Fin.elim0 := by
  let E : LinearRecurrence ℂ := ⟨0, Fin.elim0⟩
  have hcoeff : E.charPoly.coeff 0 = 1 := by
    simp [E, LinearRecurrence.charPoly]
  simpa only [hcoeff] using
    not_algebraicIndependent_linearRecurrence_solutions_pow E Fin.elim0 (fun j ↦ Fin.elim0 j)

end MathlibExtTest.NumberTheory.Recurrences.DecomposableFormLinearRecurrenceAlgebraicDependence
