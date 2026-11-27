/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RandomGraphNoIsolated

open MeasureTheory Filter Topology unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted

/-- At the center of the threshold window the probability tends to `1/e`. -/
example : ∃ p : ℕ → I, (∀ᶠ n : ℕ in atTop, (p n : ℝ) = Real.log n / n) ∧
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w}) atTop (𝓝 (Real.exp (-1))) := by
  obtain ⟨p, hp⟩ := exists_prob_eventually_eq 0
  refine ⟨p, by simpa using hp, ?_⟩
  simpa using tendsto_measureReal_no_isolated 0 p
    (tendsto_mul_sub_log_of_eventually_eq 0 _ hp)

/-- On one vertex the event has probability zero for every edge parameter. -/
example (p : I) : (randomSubsetLaw (fun _ : Pair 1 => p)).real
    {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w} = 0 := by
  have h : {ω : Pair 1 → Bool | ∀ v, ∃ w, (pairGraph ω).Adj v w} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨w, hw⟩ := hω 0
    exact hw.ne (Subsingleton.elim _ w)
  rw [h, measureReal_empty]
