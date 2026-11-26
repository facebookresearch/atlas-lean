/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Hypercontractivity.VectorTwoPoint

/-!
# The tensorization step for Bonami–Beckner hypercontractivity

The vector two-point inequality `vtp_vectorTwoPoint` gives the induction step
`bnt_TensorStep ρ` of the tensorization argument, for `0 ≤ ρ ≤ 1`.

## Main results

* `StatMech.Probability.bvtp_tensorStep`.
-/

@[expose] public section

namespace StatMech.Probability

/-- The tensorization step `bnt_TensorStep ρ` holds for `0 ≤ ρ ≤ 1`. -/
theorem bvtp_tensorStep {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    bnt_TensorStep ρ :=
  fun n ih f => bnt_tensorStep_of_vec (vtp_vectorTwoPoint h0 h1) n ih f

end StatMech.Probability
