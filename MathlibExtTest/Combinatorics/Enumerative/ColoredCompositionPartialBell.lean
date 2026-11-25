/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ColoredCompositionPartialBell

open MetaMathlibExt

/-- The partial Bell polynomial commutes with the cast `ℕ → ℚ`. -/
private theorem partialBellPolynomial_natCast (n k : ℕ) (x : ℕ → ℕ) :
    partialBellPolynomial n k (fun j => (x j : ℚ)) = ((partialBellPolynomial n k x : ℕ) : ℚ) := by
  simp [partialBellPolynomial]

-- Part `j` takes `j` colors. `decide` evaluates `B_{3,2}(x) = 3 x₁ x₂` at `x_j = j! · j` in `ℕ`
-- from the definition, and the formula turns `2!/3! · 12` into the count `4` of the colored
-- compositions `(1, 2)` and `(2, 1)` of `3`, which carry `1 · 2` colorings each.
example : coloredCompositionCount (fun j => j) 3 2 = 4 := by
  have h := coloredCompositionCount_eq_partialBell (fun j => j) (n := 3) (by norm_num) 2
  have hB : partialBellPolynomial 3 2 (fun j => j.factorial * j) = 12 := by decide
  have hcast : (fun j => (j.factorial : ℚ) * ((fun j => j) j : ℕ)) =
      fun j => ((j.factorial * j : ℕ) : ℚ) := by
    ext j
    push_cast
    rfl
  rw [hcast, partialBellPolynomial_natCast, hB] at h
  norm_num [Nat.factorial] at h
  exact_mod_cast h

-- With one color for every part it gives the Lah number `B_{3,2}(1!, 2!, 3!, …) = 6`.
example : partialBellPolynomial 3 2 (fun j => (j.factorial : ℚ)) = 6 := by
  have h := coloredCompositionCount_eq_partialBell (fun _ => 1) (n := 3) (by norm_num) 2
  rw [coloredCompositionCount_one_three_two] at h
  norm_num [Nat.factorial] at h
  linarith
