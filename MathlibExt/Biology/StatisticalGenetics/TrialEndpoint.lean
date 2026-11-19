/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Statistics.Survival.ObservedTime

/-!
# Prespecified truncated trial endpoint

Potential endpoints truncated at a prespecified horizon inherit the finite-population randomization results for difference-in-means; truncation changes event times beyond the horizon.
-/

@[expose] public section

namespace MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-- The prespecified truncated endpoint of event time `T i` at
horizon `h`: `min (T i) h`. -/
def truncatedEndpoint {ι : Type*} (T : ι → ℝ) (h : ℝ) (i : ι) : ℝ :=
  MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime.obsTime T (fun _ => h) i

/-- **Truncated endpoint at or inside the horizon.** If
`T i ≤ h`, the truncated endpoint is the event time itself. -/
lemma truncatedEndpoint_eq_of_le {ι : Type*} (T : ι → ℝ) (h : ℝ)
    (i : ι) (hi : T i ≤ h) : truncatedEndpoint T h i = T i :=
  min_eq_left hi

/-- **Truncated endpoint beyond the horizon.** If `h ≤ T i`, the
truncated endpoint is the horizon. -/
lemma truncatedEndpoint_eq_of_ge {ι : Type*} (T : ι → ℝ) (h : ℝ)
    (i : ι) (hi : h ≤ T i) : truncatedEndpoint T h i = h :=
  min_eq_right hi

/-- **Truncation changes event times beyond the horizon.** For
an event time beyond the horizon (`h < T`), the truncated
endpoint differs from the uncensored event time. -/
lemma truncation_changes_value {ι : Type*} (T : ι → ℝ) {h : ℝ}
    (i : ι) (hT : h < T i) : truncatedEndpoint T h i ≠ T i := by
  rw [truncatedEndpoint_eq_of_ge T h i (le_of_lt hT)]
  exact ne_of_lt hT

end MathlibExt.Biology.StatisticalGenetics.TrialEndpoint
