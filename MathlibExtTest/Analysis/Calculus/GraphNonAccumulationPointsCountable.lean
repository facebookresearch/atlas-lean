/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountable

/-! # Tests for isolated points of a graph -/

namespace MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted

open Filter

-- On a singleton domain there is no sequence avoiding the unique point.
example {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    ({a} : Set (EuclideanSpace ℝ (Fin n))).Countable := by
  rw [← Set.sdiff_empty (s := {a})]
  apply countable_diff_setOf_exists_seq_tendsto_and_tendsto_apply {a} ∅ f
  intro x
  constructor
  · simp
  · rintro ⟨rfl, u, hu, -⟩
    exact (hu 0).2 (hu 0).1

-- If f is constant except for a different value at a, its graph is isolated over a.
example {n : ℕ} (a b : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ha : f a ≠ b) (hoff : ∀ x ≠ a, f x = b) :
    let F := {x | ∃ u : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, u k ≠ x) ∧
      Tendsto u atTop (nhds x) ∧ Tendsto (fun k => f (u k)) atTop (nhds (f x))}
    a ∉ F ∧ Fᶜ.Countable := by
  intro F
  constructor
  · rintro ⟨u, hu, -, hfu⟩
    exact ha (tendsto_nhds_unique_of_forall hfu tendsto_const_nhds fun k => hoff _ (hu k))
  · rw [Set.compl_eq_univ_sdiff]
    exact countable_diff_setOf_exists_seq_tendsto_and_tendsto_apply Set.univ F f (by simp [F])

end MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted
