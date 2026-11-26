/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The state model and concrete instance are adapted from OpenAI's
`lean/OAI/Optimization/Tropical/TruffetModel.lean` at
`3344da59991ed94f9ba711217b29c1d760badfa6` (Apache License, Version 2.0).
See https://www.apache.org/licenses/LICENSE-2.0. The model uses Atlas imports and namespace;
no proof of the counterexample from the source is included in this module.

Source repository: https://github.com/openai/math
Authors: OpenAI (project attribution in lean/formalization.yaml).
The wanted proposition follows `lean/ComparatorChallenges/TruffetCounterexample.lean`
at the same revision. Neither source file supplies a copyright or author notice.
The source's `lean/LICENSE` names no copyright holder or authors:
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/LICENSE
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace WantedExt.MaxPlusElimination

noncomputable section

/-! # Two-column max-plus elimination state and its step rules

Coefficients live in `WithBot ℝ`, with a third coordinate that is not eliminated.
The transition and its preconditions apply to any state with two rows and two
eliminable columns, independently of the concrete execution below.
-/

abbrev Coeff := WithBot ℝ

abbrev Form := Fin 3 → Coeff

abbrev Var := Fin 2

abbrev RowIndex := Fin 2

def column (j : Var) : Fin 3 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def nullForm : Form := fun _ => ⊥

structure Row where
  lhs : Form
  rhs : Form

structure State where
  rows : RowIndex → Row
  cost : Form
  remaining : Var → Prop

def wellFormed (s : State) : Prop := ∀ j, ¬ s.remaining j →
  s.cost (column j) = ⊥ ∧ ∀ i,
    (s.rows i).lhs (column j) = ⊥ ∧ (s.rows i).rhs (column j) = ⊥

def eval (f : Form) (w : Fin 3 → ℝ) : Coeff :=
  max (f 0 + (w 0 : Coeff)) (max (f 1 + (w 1 : Coeff)) (f 2 + (w 2 : Coeff)))

def feasible (s : State) (w : Fin 3 → ℝ) : Prop :=
  ∀ i, eval (s.rows i).rhs w ≤ eval (s.rows i).lhs w

def lower (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).lhs (column j) ≠ ⊥ ∧
    (s.rows i).rhs (column j) < (s.rows i).lhs (column j)

def upper (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).rhs (column j) ≠ ⊥ ∧
    (s.rows i).lhs (column j) < (s.rows i).rhs (column j)

def dominating (s : State) (j : Var) : Prop :=
  s.remaining j ∧ (∃ i, lower s i j) ∧ ∃ i, upper s i j

def eligible (s : State) (i : RowIndex) (j : Var) : Prop :=
  s.remaining j ∧ lower s i j ∧ ((∃ k, dominating s k) → dominating s j)

def bounded (s : State) : Prop :=
  ∀ j, s.remaining j → (∃ i, lower s i j) ∨ ∃ i, upper s i j

def stop (s : State) : Prop := ∀ i, (s.rows i).rhs 2 ≤ (s.rows i).lhs 2

def switch (s : State) : Prop :=
  (∀ j, s.remaining j → s.cost (column j) = ⊥) ∧ ¬ stop s ∧
  (∃ j, s.remaining j) ∧
  (¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
  ∃ i j, s.remaining j ∧ upper s i j

def failure (s : State) : Prop := ¬ stop s ∧
  ((¬ ∃ j, s.remaining j) ∨
   ((¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
    (¬ ∃ i j, s.remaining j ∧ upper s i j)))

def lowerForm (s : State) (i : RowIndex) (j : Var) : Form := fun k =>
  if k = column j then ⊥ else
    (s.rows i).rhs k + ((-WithBot.unbotD 0 ((s.rows i).lhs (column j)) : ℝ) : Coeff)

def substitute (f : Form) (j : Var) (g : Form) : Form := fun k =>
  if k = column j then ⊥ else max (f k) (f (column j) + g k)

def cleanup (r : Row) : Row := by
  classical
  exact if ∀ k, r.rhs k ≤ r.lhs k then ⟨nullForm, nullForm⟩ else r

def advance (s : State) (i : RowIndex) (j : Var) : State where
  rows := fun r => cleanup ⟨substitute (s.rows r).lhs j (lowerForm s i j),
    substitute (s.rows r).rhs j (lowerForm s i j)⟩
  cost := substitute s.cost j (lowerForm s i j)
  remaining := fun k => s.remaining k ∧ k ≠ j

def ForcedSingletonStep (s s' : State) (i : RowIndex) (j : Var) : Prop :=
  wellFormed s ∧ wellFormed s' ∧
  bounded s ∧ ¬ stop s ∧ ¬ switch s ∧ ¬ failure s ∧
  (∀ r k, eligible s r k ↔ r = i ∧ k = j) ∧
  (∃ k, (substitute s.cost j (lowerForm s i j)) k ≠ ⊥) ∧
  s' = advance s i j

/-! ## Concrete two-step execution -/

def initial : State where
  rows := ![⟨![(0 : Coeff), 0, ⊥], ![⊥, ⊥, (0 : Coeff)]⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, (1 : Coeff), ((-2 : ℝ) : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun _ => True

def middle : State where
  rows := ![⟨nullForm, nullForm⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, ⊥, (1 : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun j => j = 0

def finalState : State where
  rows := fun _ => ⟨nullForm, nullForm⟩
  cost := ![⊥, ⊥, (1 : Coeff)]
  remaining := fun _ => False

def crossRowRestriction (s : State) : Prop :=
  ∀ i r : RowIndex, i ≠ r → ∀ α : ℝ, ∃ w : Fin 3 → ℝ,
    eval (s.rows i).lhs w < (α : Coeff) + eval (s.rows r).rhs w

def output : Fin 3 → ℝ := ![1, 0, 0]

def better : Fin 3 → ℝ := ![0, -1, 0]

/-- **A forced two-step max-plus elimination returns a nonoptimal solution.**

Use triples of coefficients in $\mathbb R\cup\{-\infty\}$, evaluated at $w=(x,y,z)$ as
$E_f(w)=\max_k(f_k+w_k)$. A row $(l,r)$ requires $E_r(w)\le E_l(w)$. Initially the two rows are
$\max(x,y)\ge z$, $x\ge\max(y+1,z-2)$, the cost is $x$ and both variables $x,y$ remain; the third
coordinate is not eliminated. For either ordering of distinct rows $i,r$ and every real $\alpha$,
there is a real triple with $E_{l_i}(w)<\alpha+E_{r_r}(w)$.

For a remaining column $j$, row $i$ is a lower row if $l_{ij}$ is finite and $r_{ij}<l_{ij}$, and
upper if $r_{ij}$ is finite and $l_{ij}<r_{ij}$. A column is dominating when it has both. An
eligible pair uses a lower row for a remaining column, and must use a dominating column if one
exists. A state is well formed if eliminated coefficients are all $-\infty$, and bounded if each
remaining column has a lower or upper row. It stops when $r_{i2}\le l_{i2}$ for both rows. If not
stopped, failure means no remaining column or no lower or upper row on any remaining column. The
switch case is the nonstopped case with remaining columns all absent from the cost, no lower row on
them, and at least one upper row.

For an eligible pair form $g_j=-\infty$ and $g_k=r_{ik}-l_{ij}$ for $k\ne j$. Set coefficient $j$ of
each row-side and the cost to $-\infty$ after replacing each other coefficient $f_k$ by
$\max(f_k,f_j+g_k)$. Delete the column from the remaining set, and replace a row by two
all-$-\infty$ forms if its new right coefficients are componentwise at most its new left
coefficients.

The first eligible pair is uniquely row $0$, column $1$ (zero-based), yielding an empty row $0$, row
$1$ equal to $x\ge z+1$, cost $x$ and just $x$ remaining. The next pair is uniquely row $1$, column
$0$, yielding two empty rows, cost $z+1$ and no remaining columns; the stop condition holds. Both
steps start well formed and bounded, and start in none of stop, switch, or failure; they preserve
well-formedness and each has at least one finite substituted cost coefficient. With $z=0$,
reconstruction by the selected lower forms gives $(1,0,0)$, feasible in the initial rows and with
initial cost equal to the final cost there. The triple $(0,-1,0)$ is also feasible and has strictly
smaller initial cost than that final cost at $(1,0,0)$.

Source: https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TruffetCounterexample.lean#L8-L129
-/
theorem_wanted finite_execution_not_optimal :
    crossRowRestriction initial ∧
    ForcedSingletonStep initial middle 0 1 ∧
    ForcedSingletonStep middle finalState 1 0 ∧
    (¬ ∃ j, finalState.remaining j) ∧ stop finalState ∧
    feasible initial output ∧ feasible initial better ∧
    output 2 = 0 ∧ better 2 = 0 ∧
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧
    eval initial.cost output = eval finalState.cost output ∧
    eval initial.cost better < eval finalState.cost output

end

end WantedExt.MaxPlusElimination
