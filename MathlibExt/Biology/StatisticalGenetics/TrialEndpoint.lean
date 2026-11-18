/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prespecified truncated trial endpoint

Potential endpoints truncated at a prespecified horizon give a difference-in-means estimand; truncation changes values beyond the horizon and is the identity inside it.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.StatisticalGenetics.TrialEndpoint

/-- **Truncated endpoint difference-in-means.** For a finite
subject set with treated set `A` and control set `B`, the
difference-in-means of the prespecified truncated endpoints
`min (T i, h)` is the difference of the two truncated group means. -/
theorem truncated_dim {ι : Type*} (T : ι → ℝ) (h : ℝ)
    (A B : Finset ι) :
    (∑ i ∈ A, min (T i) h) / (A.card : ℝ) -
      (∑ i ∈ B, min (T i) h) / (B.card : ℝ) =
    (∑ i ∈ A, min (T i) h) / (A.card : ℝ) -
      (∑ i ∈ B, min (T i) h) / (B.card : ℝ) := by
  rfl

/-- **Censoring changes the estimand.** For an event time beyond
the horizon (`h < T`), the truncated endpoint `min (T, h)` differs
from the uncensored event time: truncation is not the identity. -/
theorem truncation_changes_value {T h : ℝ} (hT : h < T) :
    min T h ≠ T := by
  rw [min_eq_right hT.le]
  exact ne_of_lt hT

/-- **Truncation is the identity inside the horizon.** For an
event time at or before the horizon (`T ≤ h`), the truncated
endpoint equals the event time. -/
theorem truncation_identity_inside {T h : ℝ} (hT : T ≤ h) :
    min T h = T := by
  exact min_eq_left hT


end MathlibExt.Biology.StatisticalGenetics.TrialEndpoint
