/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-term progressions in unit-step walks (Erdős Problem 192)

Erdős Problem 192: let `a₁, a₂, …` be an infinite sequence in `ℝ^d` such that each `aᵢ₊₁ - aᵢ` is a
standard unit vector. For which `d` must the sequence contain a three-term arithmetic progression?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #192, https://www.erdosproblems.com/192 (status SOLVED
(LEAN)). UnsolvedMath record UM-30006758 (`EP-192`), dataset ulamai/UnsolvedMath v1.8.0.

Points of `ℝ^d` are functions `Fin d → ℝ`, a step is `Pi.single j 1`, and a three-term progression
is `x, y, z` among the points with `x ≠ y` and `x + z = 2 y` (points of the walk are distinct since
the coordinate sum grows by `1` at each step). The answer is stated as an equivalence for every `d`;
for `d = 0` no such walk exists and `0 ≤ 3`. Compared with the formal-conjectures statement
`ErdosProblems/192.lean` (answer `Set.Iic 3`, equivalent; no code imported).
-/

/-- `a` is a walk in `ℝ^d` whose steps `a (i + 1) - a i` are standard unit vectors. -/
def IsUnitStepWalk (d : ℕ) (a : ℕ → Fin d → ℝ) : Prop :=
  ∀ i, ∃ j : Fin d, a (i + 1) = a i + Pi.single j 1

/-- The points of `a` contain a three-term arithmetic progression `x, y, z` with `x ≠ y`,
`x + z = 2 y`. -/
def HasThreeAP {d : ℕ} (a : ℕ → Fin d → ℝ) : Prop :=
  ∃ i j k : ℕ, a i ≠ a j ∧ a i + a k = 2 • a j

/-- Erdős Problem 192: every infinite walk in `ℝ^d` with standard unit vector steps contains a
three-term arithmetic progression if and only if `d ≤ 3`. -/
def unitStepWalkThreeAPIff : Prop :=
  ∀ d : ℕ, (∀ a : ℕ → Fin d → ℝ, IsUnitStepWalk d a → HasThreeAP a) ↔ d ≤ 3

/--
Resolved true: the progression is forced exactly when `d ≤ 3`. Points `aᵢ, aⱼ, a_k` form a
progression exactly when the step words from `i` to `j` and from `j` to `k` are permutations of each
other (an abelian square). Over at most three letters every long enough word contains an abelian
square, and Keränen's infinite abelian-square-free word over four letters gives, for every `d ≥ 4`,
a walk with no three-term progression. erdosproblems.com/192 lists the problem as solved. Source: T.
F. Bloom, Erdős Problems, Problem #192, https://www.erdosproblems.com/192 (status SOLVED (LEAN));
resolution: V. Keränen, Abelian squares are avoidable on 4 letters, Automata, Languages and
Programming (ICALP 1992), Lecture Notes in Comput. Sci. 623, Springer (1992), 41-52,
erdosproblems.com/192: true for d ≤ 3 and false for d ≥ 4, via an infinite abelian-square-free word
over 4 letters (Keränen), https://doi.org/10.1007/3-540-55719-9_62.
-/
public theorem_wanted unitStepWalkThreeAPIff_holds : unitStepWalkThreeAPIff

end MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192Wanted
