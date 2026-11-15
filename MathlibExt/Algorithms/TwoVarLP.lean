/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs

/-!
# Two-variable LP: feasibility under added constraints

A constraint `(a, b, c) : ℚ × ℚ × ℚ` means `a * x + b * y ≤ c`, and a point
`p = (x, y)` is feasible for a list of constraints when it satisfies all of
them. Feasibility is antitone in the constraint list, and a point feasible
after appending a constraint satisfies that constraint. Algorithms for
two-variable linear programming are not included here.
-/

@[expose] public section

namespace MathlibExt.Algorithms.TwoVarLP

/-- The point `p = (x, y)` satisfies every constraint `(a, b, c)` in `cs`,
that is, `a * x + b * y ≤ c`. -/
def feasible (cs : List (ℚ × ℚ × ℚ)) (p : ℚ × ℚ) : Prop :=
  ∀ c ∈ cs, c.1 * p.1 + c.2.1 * p.2 ≤ c.2.2

/-- Feasibility is antitone in the constraint list. -/
theorem feasible_mono {cs₁ cs₂ : List (ℚ × ℚ × ℚ)} {p : ℚ × ℚ}
    (h : feasible cs₂ p) (hsub : ∀ c ∈ cs₁, c ∈ cs₂) :
    feasible cs₁ p := by
  intro c hc
  exact h c (hsub c hc)

/-- A point feasible after appending the constraint `c` satisfies `c`. -/
theorem feasible_new_constraint {cs : List (ℚ × ℚ × ℚ)}
    (c : ℚ × ℚ × ℚ) {p : ℚ × ℚ} (hp : feasible (cs ++ [c]) p) :
    c.1 * p.1 + c.2.1 * p.2 ≤ c.2.2 :=
  hp c (List.mem_append_right cs (List.mem_singleton_self c))

end MathlibExt.Algorithms.TwoVarLP
