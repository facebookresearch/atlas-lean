/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.ArchetypalAnalysis
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Archetypal analysis tests

Data `0, 1, 1/2` on the real line. The sample mean `1/2` is a feasible single archetype; the
two archetypes `0, 1` (the endpoints, i.e. the boundary of the hull `[0, 1]`) reproduce every
data point, so their RSS is `0`; any feasible pair of archetypes can be moved to the boundary.
In the zero space the hull of the data is the whole space and has empty frontier, which is why
the boundary result assumes a nontrivial space.
-/

namespace Cslib.MachineLearning.ArchetypalAnalysis

open Set

private noncomputable def dat : Fin 3 → ℝ := ![0, 1, 1 / 2]

example : mean dat = 1 / 2 := by
  simp [mean, dat, Fin.sum_univ_three]; norm_num

example (z : Fin 1 → ℝ) : rss dat (fun _ : Fin 1 => mean dat) ≤ rss dat z :=
  (rss_const_mean_le dat (by norm_num) z).2

private noncomputable def ends : Fin 2 → ℝ := ![0, 1]

example : rss dat ends = 0 := by
  refine rss_eq_zero_of_subset _ _ (by norm_num) ?_
  have h : convexHull ℝ (range ends) = Icc 0 1 := by
    rw [show range ends = {0, 1} by
      ext y; simp [ends]; tauto]
    rw [convexHull_pair, segment_eq_Icc (by norm_num)]
  intro i; rw [h]; fin_cases i <;> norm_num [dat]

example (z : Fin 2 → ℝ) (hz : Feasible dat z) :
    ∃ z' : Fin 2 → ℝ, Feasible dat z' ∧ (∀ k, z' k ∈ frontier (convexHull ℝ (range dat))) ∧
      rss dat z' ≤ rss dat z := by
  obtain ⟨z', h1, h2, -, h4⟩ := exists_frontier_rss_le dat le_rfl z hz
  exact ⟨z', h1, h2, h4⟩

/-- In the zero space every hull of data is the whole space, whose frontier is empty. -/
example : frontier (univ : Set (EuclideanSpace ℝ (Fin 0))) = ∅ := frontier_univ

end Cslib.MachineLearning.ArchetypalAnalysis
