/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.Finite

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Tests for Dirichlet forms on a finite state space

* The two-state generator with jump rate `1` and an extra killing rate `1`: its form is
  `(f 0 - f 1)² + f 0² + f 1²`, the form is unit-contractive, and the generator is reversible for
  the counting measure, so the form is `-⟨f, Q f⟩`.
* The Beurling–Deny criterion accepts the graph Laplacian `!![1, -1; -1, 1]` and rejects
  `!![1, 1; 1, 1]`, for which an explicit `u` has its energy increased by the unit contraction.
-/

set_option autoImplicit false

open Matrix ProbabilityTheory
open MathlibExt.Probability.DirichletForm

namespace MathlibExtTest.Probability.DirichletForm.Finite

/-- Two states, jump rate `1` each way, killing rate `1` at each state. -/
def Q₂ : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 1; 1, -2]

example (x : Fin 2) : killingRate Q₂ x = 1 := by
  fin_cases x <;> simp [killingRate, Q₂, Fin.sum_univ_two] <;> norm_num

example (f : Fin 2 → ℝ) : form 1 Q₂ f f = (f 0 - f 1) ^ 2 + f 0 ^ 2 + f 1 ^ 2 := by
  simp [form, killingRate, Q₂, Fin.sum_univ_two]
  ring

example (f : Fin 2 → ℝ) : form 1 Q₂ f f = -∑ x, (1 : Fin 2 → ℝ) x * f x * (Q₂ *ᵥ f) x :=
  form_eq_neg_sum_mul_mulVec (fun i j => by fin_cases i <;> fin_cases j <;> simp [Q₂]) f f

/-- The form of `Q₂` has the Markov property (hypotheses are jointly satisfiable). -/
example (u : Fin 2 → ℝ) :
    form 1 Q₂ (unitContraction u) (unitContraction u) ≤ form 1 Q₂ u u :=
  form_unitContraction_le (fun _ => zero_le_one)
    (fun i j h => by fin_cases i <;> fin_cases j <;> simp [Q₂] at h ⊢)
    (fun x => by fin_cases x <;> simp [killingRate, Q₂, Fin.sum_univ_two]) u

/-- The unit contraction clamps values to `[0, 1]`. -/
example : unitContraction ![(-3 : ℝ), 5] = ![0, 1] := by
  funext x; fin_cases x <;> simp [unitContraction]

/-- The Laplacian of one edge passes the Beurling–Deny criterion. -/
example (u : Fin 2 → ℝ) :
    matrixForm !![(1 : ℝ), -1; -1, 1] (unitContraction u) (unitContraction u) ≤
      matrixForm !![(1 : ℝ), -1; -1, 1] u u := by
  refine (unitContraction_le_iff ?_).mpr ⟨fun x y h => ?_, fun x => ?_⟩ u
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · fin_cases x <;> fin_cases y <;> simp at h ⊢
  · fin_cases x <;> simp [Fin.sum_univ_two]

/-- A symmetric matrix with a positive off-diagonal entry fails it. -/
example : ¬ ∀ u : Fin 2 → ℝ,
    matrixForm !![(1 : ℝ), 1; 1, 1] (unitContraction u) (unitContraction u) ≤
      matrixForm !![(1 : ℝ), 1; 1, 1] u u := by
  rw [unitContraction_le_iff (by ext i j; fin_cases i <;> fin_cases j <;> simp)]
  rintro ⟨h, -⟩
  have := h 0 1 (by decide)
  norm_num at this

/-- Explicitly: `u = (1, -1)` has energy `0`, its contraction `(1, 0)` has energy `1`. -/
example : matrixForm !![(1 : ℝ), 1; 1, 1] ![1, -1] ![1, -1] = 0 ∧
    matrixForm !![(1 : ℝ), 1; 1, 1] (unitContraction ![1, -1])
      (unitContraction ![1, -1]) = 1 := by
  have hc : unitContraction ![(1 : ℝ), -1] = ![1, 0] := by
    funext x; fin_cases x <;> simp [unitContraction]
  rw [hc]
  constructor <;> simp [matrixForm, dotProduct, mulVec, Fin.sum_univ_two]

end MathlibExtTest.Probability.DirichletForm.Finite
