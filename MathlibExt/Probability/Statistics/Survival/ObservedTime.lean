/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Observed time

The observed time of a latent event time and a censoring time is their minimum. This lightweight definition is shared by survival and endpoint modules without importing the counting-process development.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

/-- The observed time `min (T i) (C i)` of latent event time `T`
and censoring time `C` for subject `i`. -/
def obsTime {ι : Type*} (T C : ι → ℝ) (i : ι) : ℝ :=
  min (T i) (C i)

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
