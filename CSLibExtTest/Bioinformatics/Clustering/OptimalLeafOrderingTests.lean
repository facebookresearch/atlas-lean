/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Clustering.OptimalLeafOrdering
public import Mathlib.Tactic.NormNum

/-!
# Optimal leaf ordering tests

The dendrogram `((1, 2), 3)` has two internal nodes and four leaf orders. With the similarity
`S a b = 1` if `{a, b} = {1, 3}` and `0` otherwise, the best order puts `1` next to `3`:
`[2, 1, 3]` (or its reverse) scores `1`. A single leaf has one order, of score `0`; repeated
labels are allowed.
-/

namespace Cslib.Bioinformatics.Clustering.OptimalLeafOrdering

open Dendrogram

private def t3 : Dendrogram ℕ := .node (.node (.leaf 1) (.leaf 2)) (.leaf 3)

example : orderings t3 = [[1, 2, 3], [2, 1, 3], [3, 1, 2], [3, 2, 1]] := rfl

example : (orderings t3).length = 2 ^ numInternal t3 := length_orderings t3

example : numInternal t3 = 2 := rfl

example : leaves t3 = [1, 2, 3] := rfl

private noncomputable def sim : ℕ → ℕ → ℝ := fun a b =>
  if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 1 else 0

example : adjScore sim [2, 1, 3] = 1 := by norm_num [adjScore, sim]

example : adjScore sim [1, 2, 3] = 0 := by norm_num [adjScore, sim]

/-- The best leaf order of `t3` scores `1`. -/
example : optScore sim t3 = 1 := by
  simp only [optScore, orderings, t3]
  norm_num [adjScore, sim, List.maximum_cons]

/-- A single leaf has the single order `[a]`, of score `0`, and the recursion agrees. -/
example (a : ℕ) : bestEnds sim (.leaf a) a a = 0 := by simp [bestEnds]

example (a : ℕ) : optEnds sim (.leaf a) a a = 0 := by
  rw [← bestEnds_eq_optEnds]; simp [bestEnds]

/-- Impossible end pairs get `⊥`. -/
example : bestEnds sim (.leaf 1) 1 2 = ⊥ := by simp [bestEnds]

/-- Repeated labels: both leaf orders of `(1, 1)` are `[1, 1]`. -/
example : orderings (.node (.leaf 1) (.leaf (1 : ℕ))) = [[1, 1], [1, 1]] := rfl

example : [3, 1, 2].Perm (leaves t3) := perm_of_mem_orderings (by decide)

end Cslib.Bioinformatics.Clustering.OptimalLeafOrdering
