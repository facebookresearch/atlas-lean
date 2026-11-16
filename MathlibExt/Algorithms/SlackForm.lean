/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Slack-form correspondence

For a standard-form system `A x = b`, `x ≥ 0`, the slack
variables defined by the equations are forced to equal
`b` on solutions, and a point satisfying the slack
relation with `y = b` and `x ≥ 0` is a solution. Pivot
equivalence is not included here.
-/

@[expose] public section

/-- Slack-form conversion core (ALG-30a). A standard-form
system `A x = b`, `x ≥ 0` (vectors as functions on `Fin n`,
equations on `Fin m`). The slack extension adds variables
`y : Fin m → ℚ` constrained to equal `A x`... here the
feasibility correspondence: any `x` satisfying the system
extends to a pair `(x, y)` with `y = b` componentwise from
the equations, and conversely a pair with the slack
relation and `y = b` projects to a solution. Formal core:
define the solution sets as predicates and prove the
projection/extension correspondence. -/
def IsSolution {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Prop :=
  (∀ i, ∑ j, A i j * x j = b i) ∧ ∀ j, 0 ≤ x j

/-- The slack variables are forced: if `∑ j, A i j * x j =
y i` for all `i` and `x` is a solution, then `y = b`. -/
theorem slack_eq {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hslack : ∀ i, ∑ j, A i j * x j = y i)
    (hx : IsSolution A b x) : y = b := by
  funext i
  rw [← hslack i]
  exact hx.1 i

/-- Conversely if the slack relation holds with `y = b` and
`x ≥ 0`, then `x` is a solution. -/
theorem solution_of_slack {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (x : Fin n → ℚ)
    (hslack : ∀ i, ∑ j, A i j * x j = b i)
    (hx : ∀ j, 0 ≤ x j) : IsSolution A b x := by
  exact ⟨hslack, hx⟩

#print axioms slack_eq
#print axioms solution_of_slack

end
