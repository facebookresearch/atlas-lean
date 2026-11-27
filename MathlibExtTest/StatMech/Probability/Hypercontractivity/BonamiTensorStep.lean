/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.BonamiTensorStep

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.BonamiTensorStep`

* The tensorization step `bnt_TensorStep` at `ρ = 1/2`.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTensorStep

example : bnt_TensorStep (1 / 2) := bvtp_tensorStep (by norm_num) (by norm_num)

end MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTensorStep
