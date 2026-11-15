/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
public import Mathlib.Data.List.Basic

/-!
# Incremental two-variable LP: feasibility facts

Constraints `(a, b, c)` mean `a * x + b * y ≤ c` over `ℚ`.
Feasibility is antitone in the constraint list, and a point
feasible after adding a constraint satisfies that
constraint. The randomized incremental analysis is not
included here.
-/

@[expose] public section

/-- Two-variable linear programming, incremental core
(ALG-48). A constraint is `(a, b, c) : ℚ × ℚ × ℚ` meaning
`a * x + b * y ≤ c`. The feasible set after a list of
constraints, as a predicate. -/
def feasible (cs : List (ℚ × ℚ × ℚ)) (p : ℚ × ℚ) : Prop :=
  ∀ c ∈ cs, c.1 * p.1 + c.2.1 * p.2 ≤ c.2.2

/-- Feasibility is antitone in the constraint list. -/
theorem feasible_mono {cs₁ cs₂ : List (ℚ × ℚ × ℚ)} {p : ℚ × ℚ}
    (h : feasible cs₂ p) (hsub : ∀ c ∈ cs₁, c ∈ cs₂) :
    feasible cs₁ p := by
  intro c hc
  exact h c (hsub c hc)

/-- Optimal value of a bounded LP is attained at a vertex:
for a single constraint line and objective `x`, the minimum
over the half-plane... too specific; instead the incremental
step invariant: if `p` is feasible for `cs` and violates the
new constraint `c`, any feasible point `q` for `cs ++ [c]`
lies on the line of `c` or beyond in the violated direction:
`c.1 * q.1 + c.2.1 * q.2 ≤ c.2.2 < c.1 * p.1 + c.2.1 * p.2`. -/
theorem feasible_new_constraint {cs : List (ℚ × ℚ × ℚ)}
    (c : ℚ × ℚ × ℚ) {p q : ℚ × ℚ}
    (hp : feasible cs p) (hviol : c.2.2 < c.1 * p.1 + c.2.1 * p.2)
    (hq : feasible (cs ++ [c]) q) :
    c.1 * q.1 + c.2.1 * q.2 ≤ c.2.2 := by
  exact hq c (List.mem_append_right cs (List.mem_singleton_self c))

end
