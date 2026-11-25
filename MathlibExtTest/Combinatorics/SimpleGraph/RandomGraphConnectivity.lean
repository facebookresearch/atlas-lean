/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivity

open MeasureTheory Filter Topology unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted

/-- At the center of the threshold window the limiting connectivity probability is 1/e. -/
example : ∃ p : ℕ → I, (∀ᶠ n : ℕ in atTop, (p n : ℝ) = Real.log n / n) ∧
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).Connected}) atTop (𝓝 (Real.exp (-1))) := by
  obtain ⟨p, hp⟩ := exists_prob_eventually_eq 0
  exact ⟨p, by simpa using hp, by simpa using tendsto_measureReal_connected 0 p hp⟩

/-- A single vertex is connected even though it has no neighbor. -/
example (p : I) : (randomSubsetLaw (fun _ : Pair 1 => p)).real
    {ω | (pairGraph ω).Connected} = 1 := by
  have h : {ω : Pair 1 → Bool | (pairGraph ω).Connected} = Set.univ :=
    Set.eq_univ_of_forall fun _ => SimpleGraph.Connected.of_subsingleton
  rw [h, probReal_univ]
