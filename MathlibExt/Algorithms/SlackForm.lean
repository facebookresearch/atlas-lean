/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Slack form of a system of linear inequalities

A system of linear inequalities `A x ≤ b`, `x ≥ 0` over `ℚ`, with `m` constraints and `n`
variables (`A : Matrix (Fin m) (Fin n) ℚ`, inequalities componentwise), becomes the system of
equations `A x + s = b` with sign constraints `x ≥ 0`, `s ≥ 0` by adding one slack variable
`s i` per constraint. This is the conversion of the constraints of a linear program from
standard form to slack form in Cormen, Leiserson, Rivest and Stein, Section 29.1. Only the
constraints are modelled here, not the objective function.

* `Feasible A b x`: `A x ≤ b` and `x ≥ 0`.
* `SlackFeasible A b x s`: `A x + s = b`, `x ≥ 0` and `s ≥ 0`.
* `slackFeasible_of_feasible` (extension): a feasible `x` together with the slack `b - A x` is
  slack-feasible.
* `feasible_of_slackFeasible` (projection): the `x` part of a slack-feasible pair is feasible.
* `slack_eq_of_slackFeasible`: the slack of a slack-feasible pair is determined by `x`, namely
  `s = b - A x`.
* `feasible_iff_exists_slackFeasible`: `x` is feasible exactly when some slack vector `s` makes
  `(x, s)` slack-feasible.

## References

* T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  3rd ed., MIT Press, 2009, Section 29.1.
-/

@[expose] public section

namespace MathlibExt.Algorithms.SlackForm

open Matrix

variable {m n : ℕ}

/-- `x` is a feasible point of the system `A x ≤ b`, `x ≥ 0`, with both inequalities read
componentwise. -/
def Feasible (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ) : Prop :=
  (∀ i, (A *ᵥ x) i ≤ b i) ∧ ∀ j, 0 ≤ x j

/-- `(x, s)` is a feasible point of the slack form `A x + s = b`, `x ≥ 0`, `s ≥ 0` of the system
`A x ≤ b`, `x ≥ 0`: the slack variable `s i` is the gap in constraint `i`. -/
def SlackFeasible (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ)
    (s : Fin m → ℚ) : Prop :=
  (∀ i, (A *ᵥ x) i + s i = b i) ∧ (∀ j, 0 ≤ x j) ∧ ∀ i, 0 ≤ s i

variable {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {x : Fin n → ℚ} {s : Fin m → ℚ}

/-- Extension: a feasible point `x` together with the slack `b - A x` is slack-feasible. -/
theorem slackFeasible_of_feasible (h : Feasible A b x) :
    SlackFeasible A b x (b - A *ᵥ x) :=
  ⟨fun i => add_sub_cancel ((A *ᵥ x) i) (b i), h.2, fun i => sub_nonneg.mpr (h.1 i)⟩

/-- Projection: the `x` part of a slack-feasible pair is feasible. -/
theorem feasible_of_slackFeasible (h : SlackFeasible A b x s) : Feasible A b x :=
  ⟨fun i => h.1 i ▸ le_add_of_nonneg_right (h.2.2 i), h.2.1⟩

/-- The slack variables are forced by the equations: the slack of a slack-feasible pair is
`b - A x`. -/
theorem slack_eq_of_slackFeasible (h : SlackFeasible A b x s) : s = b - A *ᵥ x :=
  funext fun i => eq_sub_of_add_eq' (h.1 i)

/-- `x` is feasible exactly when some slack vector `s` makes `(x, s)` slack-feasible. -/
theorem feasible_iff_exists_slackFeasible :
    Feasible A b x ↔ ∃ s, SlackFeasible A b x s :=
  ⟨fun h => ⟨_, slackFeasible_of_feasible h⟩, fun ⟨_, h⟩ => feasible_of_slackFeasible h⟩

end MathlibExt.Algorithms.SlackForm
