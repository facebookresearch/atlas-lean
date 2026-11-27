/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction
import Mathlib.Tactic.NormNum

/-!
# Tests for Razborov's triangle density function

Values at the Turán densities `1 - 1/(t+1)`: `h(2/3) = 2/9` (where Goodman's bound
`a (2 a - 1) = 2/9` is tight), `h(3/4) = 3/8`, and `h = 0` up to edge density `1/2`.
-/

open MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction

namespace MathlibExtTest.Combinatorics.SimpleGraph.RazborovTriangleFunction

example : razborovTriangleDensity (1 / 2) = 0 :=
  razborovTriangleDensity_of_le_half le_rfl

example : razborovTriangleDensity (1 / 3) = 0 :=
  razborovTriangleDensity_of_le_half (by norm_num)

/-- At `a = 2/3` (balanced complete tripartite graph): `h(2/3) = 2/9 = a (2 a - 1)`. -/
example : razborovTriangleDensity (2 / 3) = 2 / 9 ∧ (2 / 3 : ℝ) * (2 * (2 / 3) - 1) = 2 / 9 := by
  refine ⟨?_, by norm_num⟩
  have h := razborovTriangleDensity_one_sub_inv (t := 2) le_rfl
  norm_num at h
  exact h

/-- At `a = 3/4` (balanced complete `4`-partite graph): `h(3/4) = 3/8`. -/
example : razborovTriangleDensity (3 / 4) = 3 / 8 := by
  have h := razborovTriangleDensity_one_sub_inv (t := 3) (by norm_num)
  norm_num at h
  exact h

end MathlibExtTest.Combinatorics.SimpleGraph.RazborovTriangleFunction
