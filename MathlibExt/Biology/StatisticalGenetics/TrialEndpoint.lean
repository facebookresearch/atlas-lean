/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Prespecified truncated trial endpoint

Potential endpoints truncated at a prespecified horizon inherit the finite-population randomization results for difference-in-means; truncation changes event times beyond the horizon.
-/

@[expose] public section

namespace MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-- The prespecified truncated endpoint of event time `T i` at
horizon `h`: `min (T i) h`. -/
def truncatedEndpoint {ι : Type*} (T : ι → ℝ) (h : ℝ) (i : ι) : ℝ :=
  min (T i) h

/-- **Truncated endpoints inherit difference-in-means
unbiasedness.** Under complete randomization with at least one
treated and one control unit, the difference-in-means of the
prespecified truncated potential endpoints is unbiased for their
finite-population average treatment effect. This is
`randExp_diffInMeans` applied to the truncated outcomes. -/
lemma truncated_endpoint_unbiased {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T0 T1 : ι → ℝ) (h : ℝ) {n1 : ℕ} (h1 : 1 ≤ n1)
    (h0 : n1 + 1 ≤ Fintype.card ι) :
    MathlibExt.Probability.Causality.randExp n1
        (MathlibExt.Probability.Causality.diffInMeans
          (truncatedEndpoint T0 h) (truncatedEndpoint T1 h)) =
      MathlibExt.Probability.Causality.ate
        (truncatedEndpoint T0 h) (truncatedEndpoint T1 h) :=
  MathlibExt.Probability.Causality.randExp_diffInMeans _ _ h1 h0

/-- **Truncation changes event times beyond the horizon.** For
an event time beyond the horizon (`h < T`), the truncated
endpoint differs from the uncensored event time. -/
lemma truncation_changes_value {T h : ℝ} (hT : h < T) :
    min T h ≠ T := by
  rw [min_eq_right (le_of_lt hT)]
  exact ne_of_lt hT

end MathlibExt.Biology.StatisticalGenetics.TrialEndpoint
